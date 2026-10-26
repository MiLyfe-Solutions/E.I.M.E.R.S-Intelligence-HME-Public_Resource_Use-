import V185TrunkScan23Chunk0979

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5801136 : List Nat := [2, 1, 1, 1, 2, 1, 2, 3, 1, 7, 2]
def baseStart_5801136 : Nat := 118140960795 + 5801136 * 2 ^ 59
def prefixEnd_5801136 : Nat := 4983230072969 + 3 ^ 40 * 5801136 * 2
def baseEnd_5801136 : Nat := 2978771110100920262421067

theorem tailTrace_5801136 : CollatzResearch.WordTrace tailWord_5801136 prefixEnd_5801136 2978771110100920262421067 := by
  unfold tailWord_5801136
  simp only [CollatzResearch.WordTrace]
  refine ⟨105792406155741250997931631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141056541540988334663908841 105792406155741250997931631)
  ·
    refine ⟨158688609233611876496897447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105792406155741250997931631 158688609233611876496897447)
    ·
      refine ⟨238032913850417814745346171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158688609233611876496897447 238032913850417814745346171)
      ·
        refine ⟨357049370775626722118019257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238032913850417814745346171 357049370775626722118019257)
        ·
          refine ⟨267787028081720041588514443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 357049370775626722118019257 267787028081720041588514443)
          ·
            refine ⟨401680542122580062382771665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267787028081720041588514443 401680542122580062382771665)
            ·
              refine ⟨301260406591935046787078749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 401680542122580062382771665 301260406591935046787078749)
              ·
                refine ⟨112972652471975642545154531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 301260406591935046787078749 112972652471975642545154531)
                ·
                  refine ⟨169458978707963463817731797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112972652471975642545154531 169458978707963463817731797)
                  ·
                    refine ⟨3971694813467893683228089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 169458978707963463817731797 3971694813467893683228089)
                    ·
                      refine ⟨2978771110100920262421067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3971694813467893683228089 2978771110100920262421067)
                      ·
                        rfl

theorem cell23_5801136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 1, 7, 2].length) (baseStart_5801136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5801136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5801136 prefixEnd_5801136 := by exact prefixLift 5801136
  have htrace : WordTrace (prefixWord ++ tailWord_5801136) baseStart_5801136 baseEnd_5801136 := by
    simpa [prefixWord, tailWord_5801136, baseEnd_5801136] using wordTrace_append hprefix tailTrace_5801136
  have hstable : (prefixWord ++ tailWord_5801136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5801136).length < 2 ^ (prefixWord ++ tailWord_5801136).sum := by decide
  have hdescent : baseEnd_5801136 < baseStart_5801136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5801136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5801139 : List Nat := [1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 7]
def baseStart_5801139 : Nat := 118140960795 + 5801139 * 2 ^ 59
def prefixEnd_5801139 : Nat := 4983230072969 + 3 ^ 40 * 5801139 * 2
def baseEnd_5801139 : Nat := 2978772650542883750683553

theorem tailTrace_5801139 : CollatzResearch.WordTrace tailWord_5801139 prefixEnd_5801139 2978772650542883750683553 := by
  unfold tailWord_5801139
  simp only [CollatzResearch.WordTrace]
  refine ⟨211584921730471633508222471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141056614486981089005481647 211584921730471633508222471)
  ·
    refine ⟨317377382595707450262333707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211584921730471633508222471 317377382595707450262333707)
    ·
      refine ⟨476066073893561175393500561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317377382595707450262333707 476066073893561175393500561)
      ·
        refine ⟨357049555420170881545125421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 476066073893561175393500561 357049555420170881545125421)
        ·
          refine ⟨133893583282564080579422033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 357049555420170881545125421 133893583282564080579422033)
          ·
            refine ⟨100420187461923060434566525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133893583282564080579422033 100420187461923060434566525)
            ·
              refine ⟨37657570298221147662962447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100420187461923060434566525 37657570298221147662962447)
              ·
                refine ⟨56486355447331721494443671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37657570298221147662962447 56486355447331721494443671)
                ·
                  refine ⟨84729533170997582241665507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56486355447331721494443671 84729533170997582241665507)
                  ·
                    refine ⟨127094299756496373362498261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 84729533170997582241665507 127094299756496373362498261)
                    ·
                      refine ⟨2978772650542883750683553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 127094299756496373362498261 2978772650542883750683553)
                      ·
                        rfl

theorem cell23_5801139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 7].length) (baseStart_5801139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5801139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5801139 prefixEnd_5801139 := by exact prefixLift 5801139
  have htrace : WordTrace (prefixWord ++ tailWord_5801139) baseStart_5801139 baseEnd_5801139 := by
    simpa [prefixWord, tailWord_5801139, baseEnd_5801139] using wordTrace_append hprefix tailTrace_5801139
  have hstable : (prefixWord ++ tailWord_5801139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5801139).length < 2 ^ (prefixWord ++ tailWord_5801139).sum := by decide
  have hdescent : baseEnd_5801139 < baseStart_5801139 := by decide
  rcases family_descends (prefixWord ++ tailWord_5801139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5801159 : List Nat := [1, 1, 4, 1, 1, 1, 1, 3, 2, 8]
def baseStart_5801159 : Nat := 118140960795 + 5801159 * 2 ^ 59
def prefixEnd_5801159 : Nat := 4983230072969 + 3 ^ 40 * 5801159 * 2
def baseEnd_5801159 : Nat := 992927640051991224144487

theorem tailTrace_5801159 : CollatzResearch.WordTrace tailWord_5801159 prefixEnd_5801159 992927640051991224144487 := by
  unfold tailWord_5801159
  simp only [CollatzResearch.WordTrace]
  refine ⟨211585651190399176923950531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141057100793599451282633687 211585651190399176923950531)
  ·
    refine ⟨317378476785598765385925797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211585651190399176923950531 317378476785598765385925797)
    ·
      refine ⟨59508464397299768509861087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 317378476785598765385925797 59508464397299768509861087)
      ·
        refine ⟨89262696595949652764791631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59508464397299768509861087 89262696595949652764791631)
        ·
          refine ⟨133894044893924479147187447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89262696595949652764791631 133894044893924479147187447)
          ·
            refine ⟨200841067340886718720781171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133894044893924479147187447 200841067340886718720781171)
            ·
              refine ⟨301261601011330078081171757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200841067340886718720781171 301261601011330078081171757)
              ·
                refine ⟨112973100379248779280439409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 301261601011330078081171757 112973100379248779280439409)
                ·
                  refine ⟨84729825284436584460329557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112973100379248779280439409 84729825284436584460329557)
                  ·
                    refine ⟨992927640051991224144487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 84729825284436584460329557 992927640051991224144487)
                    ·
                      rfl

theorem cell23_5801159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 8].length) (baseStart_5801159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5801159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5801159 prefixEnd_5801159 := by exact prefixLift 5801159
  have htrace : WordTrace (prefixWord ++ tailWord_5801159) baseStart_5801159 baseEnd_5801159 := by
    simpa [prefixWord, tailWord_5801159, baseEnd_5801159] using wordTrace_append hprefix tailTrace_5801159
  have hstable : (prefixWord ++ tailWord_5801159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5801159).length < 2 ^ (prefixWord ++ tailWord_5801159).sum := by decide
  have hdescent : baseEnd_5801159 < baseStart_5801159 := by decide
  rcases family_descends (prefixWord ++ tailWord_5801159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5801206 : List Nat := [5, 1, 1, 1, 1, 1, 1, 2, 10]
def baseStart_5801206 : Nat := 118140960795 + 5801206 * 2 ^ 59
def prefixEnd_5801206 : Nat := 4983230072969 + 3 ^ 40 * 5801206 * 2
def baseEnd_5801206 : Nat := 330978561527414998727305

theorem tailTrace_5801206 : CollatzResearch.WordTrace tailWord_5801206 prefixEnd_5801206 330978561527414998727305 := by
  unfold tailWord_5801206
  simp only [CollatzResearch.WordTrace]
  refine ⟨13224210338826806496931967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141058243614152602633940981 13224210338826806496931967)
  ·
    refine ⟨19836315508240209745397951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13224210338826806496931967 19836315508240209745397951)
    ·
      refine ⟨29754473262360314618096927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19836315508240209745397951 29754473262360314618096927)
      ·
        refine ⟨44631709893540471927145391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29754473262360314618096927 44631709893540471927145391)
        ·
          refine ⟨66947564840310707890718087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44631709893540471927145391 66947564840310707890718087)
          ·
            refine ⟨100421347260466061836077131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66947564840310707890718087 100421347260466061836077131)
            ·
              refine ⟨150632020890699092754115697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100421347260466061836077131 150632020890699092754115697)
              ·
                refine ⟨112974015668024319565586773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150632020890699092754115697 112974015668024319565586773)
                ·
                  refine ⟨330978561527414998727305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 112974015668024319565586773 330978561527414998727305)
                  ·
                    rfl

theorem cell23_5801206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 10].length) (baseStart_5801206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5801206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5801206 prefixEnd_5801206 := by exact prefixLift 5801206
  have htrace : WordTrace (prefixWord ++ tailWord_5801206) baseStart_5801206 baseEnd_5801206 := by
    simpa [prefixWord, tailWord_5801206, baseEnd_5801206] using wordTrace_append hprefix tailTrace_5801206
  have hstable : (prefixWord ++ tailWord_5801206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5801206).length < 2 ^ (prefixWord ++ tailWord_5801206).sum := by decide
  have hdescent : baseEnd_5801206 < baseStart_5801206 := by decide
  rcases family_descends (prefixWord ++ tailWord_5801206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5801220 : List Nat := [2, 3, 2, 2, 2, 1, 3, 1, 2, 2, 3]
def baseStart_5801220 : Nat := 118140960795 + 5801220 * 2 ^ 59
def prefixEnd_5801220 : Nat := 4983230072969 + 3 ^ 40 * 5801220 * 2
def baseEnd_5801220 : Nat := 2978814242475897933770681

theorem tailTrace_5801220 : CollatzResearch.WordTrace tailWord_5801220 prefixEnd_5801220 2978814242475897933770681 := by
  unfold tailWord_5801220
  simp only [CollatzResearch.WordTrace]
  refine ⟨105793938021589092170960557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141058584028785456227947409 105793938021589092170960557)
  ·
    refine ⟨39672726758095909564110209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105793938021589092170960557 39672726758095909564110209)
    ·
      refine ⟨29754545068571932173082657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39672726758095909564110209 29754545068571932173082657)
      ·
        refine ⟨22315908801428949129811993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29754545068571932173082657 22315908801428949129811993)
        ·
          refine ⟨16736931601071711847358995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22315908801428949129811993 16736931601071711847358995)
          ·
            refine ⟨25105397401607567771038493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16736931601071711847358995 25105397401607567771038493)
            ·
              refine ⟨9414524025602837914139435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25105397401607567771038493 9414524025602837914139435)
              ·
                refine ⟨14121786038404256871209153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9414524025602837914139435 14121786038404256871209153)
                ·
                  refine ⟨10591339528803192653406865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14121786038404256871209153 10591339528803192653406865)
                  ·
                    refine ⟨7943504646602394490055149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10591339528803192653406865 7943504646602394490055149)
                    ·
                      refine ⟨2978814242475897933770681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7943504646602394490055149 2978814242475897933770681)
                      ·
                        rfl

theorem cell23_5801220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_5801220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5801220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5801220 prefixEnd_5801220 := by exact prefixLift 5801220
  have htrace : WordTrace (prefixWord ++ tailWord_5801220) baseStart_5801220 baseEnd_5801220 := by
    simpa [prefixWord, tailWord_5801220, baseEnd_5801220] using wordTrace_append hprefix tailTrace_5801220
  have hstable : (prefixWord ++ tailWord_5801220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5801220).length < 2 ^ (prefixWord ++ tailWord_5801220).sum := by decide
  have hdescent : baseEnd_5801220 < baseStart_5801220 := by decide
  rcases family_descends (prefixWord ++ tailWord_5801220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5801233 : List Nat := [1, 2, 2, 1, 1, 4, 1, 2, 5, 1, 3]
def baseStart_5801233 : Nat := 118140960795 + 5801233 * 2 ^ 59
def prefixEnd_5801233 : Nat := 4983230072969 + 3 ^ 40 * 5801233 * 2
def baseEnd_5801233 : Nat := 2978820917724406382908121

theorem tailTrace_5801233 : CollatzResearch.WordTrace tailWord_5801233 prefixEnd_5801233 2978820917724406382908121 := by
  unfold tailWord_5801233
  simp only [CollatzResearch.WordTrace]
  refine ⟨211588350192131087562144353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141058900128087391708096235 211588350192131087562144353)
  ·
    refine ⟨158691262644098315671608265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211588350192131087562144353 158691262644098315671608265)
    ·
      refine ⟨119018446983073736753706199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158691262644098315671608265 119018446983073736753706199)
      ·
        refine ⟨178527670474610605130559299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119018446983073736753706199 178527670474610605130559299)
        ·
          refine ⟨267791505711915907695838949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178527670474610605130559299 267791505711915907695838949)
          ·
            refine ⟨50210907320984232692969803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 267791505711915907695838949 50210907320984232692969803)
            ·
              refine ⟨75316360981476349039454705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50210907320984232692969803 75316360981476349039454705)
              ·
                refine ⟨56487270736107261779591029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75316360981476349039454705 56487270736107261779591029)
                ·
                  refine ⟨5295681631510055791836659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56487270736107261779591029 5295681631510055791836659)
                  ·
                    refine ⟨7943522447265083687754989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5295681631510055791836659 7943522447265083687754989)
                    ·
                      refine ⟨2978820917724406382908121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7943522447265083687754989 2978820917724406382908121)
                      ·
                        rfl

theorem cell23_5801233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 5, 1, 3].length) (baseStart_5801233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5801233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5801233 prefixEnd_5801233 := by exact prefixLift 5801233
  have htrace : WordTrace (prefixWord ++ tailWord_5801233) baseStart_5801233 baseEnd_5801233 := by
    simpa [prefixWord, tailWord_5801233, baseEnd_5801233] using wordTrace_append hprefix tailTrace_5801233
  have hstable : (prefixWord ++ tailWord_5801233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5801233).length < 2 ^ (prefixWord ++ tailWord_5801233).sum := by decide
  have hdescent : baseEnd_5801233 < baseStart_5801233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5801233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5801243 : List Nat := [1, 1, 1, 1, 1, 1, 5, 3, 4, 3, 2]
def baseStart_5801243 : Nat := 118140960795 + 5801243 * 2 ^ 59
def prefixEnd_5801243 : Nat := 4983230072969 + 3 ^ 40 * 5801243 * 2
def baseEnd_5801243 : Nat := 2978826052530951343783075

theorem tailTrace_5801243 : CollatzResearch.WordTrace tailWord_5801243 prefixEnd_5801243 2978826052530951343783075 := by
  unfold tailWord_5801243
  simp only [CollatzResearch.WordTrace]
  refine ⟨211588714922094859270008383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141059143281396572846672255 211588714922094859270008383)
  ·
    refine ⟨317383072383142288905012575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211588714922094859270008383 317383072383142288905012575)
    ·
      refine ⟨476074608574713433357518863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317383072383142288905012575 476074608574713433357518863)
      ·
        refine ⟨714111912862070150036278295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 476074608574713433357518863 714111912862070150036278295)
        ·
          refine ⟨1071167869293105225054417443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 714111912862070150036278295 1071167869293105225054417443)
          ·
            refine ⟨1606751803939657837581626165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1071167869293105225054417443 1606751803939657837581626165)
            ·
              refine ⟨150632981619342922273277453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1606751803939657837581626165 150632981619342922273277453)
              ·
                refine ⟨56487368107253595852479045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150632981619342922273277453 56487368107253595852479045)
                ·
                  refine ⟨10591381520110049222339821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56487368107253595852479045 10591381520110049222339821)
                  ·
                    refine ⟨3971768070041268458377433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10591381520110049222339821 3971768070041268458377433)
                    ·
                      refine ⟨2978826052530951343783075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3971768070041268458377433 2978826052530951343783075)
                      ·
                        rfl

theorem cell23_5801243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 4, 3, 2].length) (baseStart_5801243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5801243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5801243 prefixEnd_5801243 := by exact prefixLift 5801243
  have htrace : WordTrace (prefixWord ++ tailWord_5801243) baseStart_5801243 baseEnd_5801243 := by
    simpa [prefixWord, tailWord_5801243, baseEnd_5801243] using wordTrace_append hprefix tailTrace_5801243
  have hstable : (prefixWord ++ tailWord_5801243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5801243).length < 2 ^ (prefixWord ++ tailWord_5801243).sum := by decide
  have hdescent : baseEnd_5801243 < baseStart_5801243 := by decide
  rcases family_descends (prefixWord ++ tailWord_5801243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5801290 : List Nat := [3, 1, 2, 1, 1, 1, 1, 4, 5, 2, 2]
def baseStart_5801290 : Nat := 118140960795 + 5801290 * 2 ^ 59
def prefixEnd_5801290 : Nat := 4983230072969 + 3 ^ 40 * 5801290 * 2
def baseEnd_5801290 : Nat := 2978850186121712659895359

theorem tailTrace_5801290 : CollatzResearch.WordTrace tailWord_5801290 prefixEnd_5801290 2978850186121712659895359 := by
  unfold tailWord_5801290
  simp only [CollatzResearch.WordTrace]
  refine ⟨52897607288231146574242331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141060286101949724197979549 52897607288231146574242331)
  ·
    refine ⟨79346410932346719861363497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52897607288231146574242331 79346410932346719861363497)
    ·
      refine ⟨59509808199260039896022623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79346410932346719861363497 59509808199260039896022623)
      ·
        refine ⟨89264712298890059844033935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59509808199260039896022623 89264712298890059844033935)
        ·
          refine ⟨133897068448335089766050903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89264712298890059844033935 133897068448335089766050903)
          ·
            refine ⟨200845602672502634649076355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133897068448335089766050903 200845602672502634649076355)
            ·
              refine ⟨301268404008753951973614533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200845602672502634649076355 301268404008753951973614533)
              ·
                refine ⟨56487825751641365995052725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 301268404008753951973614533 56487825751641365995052725)
                ·
                  refine ⟨5295733664216378062036193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56487825751641365995052725 5295733664216378062036193)
                  ·
                    refine ⟨3971800248162283546527145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5295733664216378062036193 3971800248162283546527145)
                    ·
                      refine ⟨2978850186121712659895359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3971800248162283546527145 2978850186121712659895359)
                      ·
                        rfl

theorem cell23_5801290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 5, 2, 2].length) (baseStart_5801290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5801290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5801290 prefixEnd_5801290 := by exact prefixLift 5801290
  have htrace : WordTrace (prefixWord ++ tailWord_5801290) baseStart_5801290 baseEnd_5801290 := by
    simpa [prefixWord, tailWord_5801290, baseEnd_5801290] using wordTrace_append hprefix tailTrace_5801290
  have hstable : (prefixWord ++ tailWord_5801290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5801290).length < 2 ^ (prefixWord ++ tailWord_5801290).sum := by decide
  have hdescent : baseEnd_5801290 < baseStart_5801290 := by decide
  rcases family_descends (prefixWord ++ tailWord_5801290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5801300 : List Nat := [2, 4, 1, 1, 2, 1, 2, 4, 2, 4]
def baseStart_5801300 : Nat := 118140960795 + 5801300 * 2 ^ 59
def prefixEnd_5801300 : Nat := 4983230072969 + 3 ^ 40 * 5801300 * 2
def baseEnd_5801300 : Nat := 992951773642752540256771

theorem tailTrace_5801300 : CollatzResearch.WordTrace tailWord_5801300 prefixEnd_5801300 992951773642752540256771 := by
  unfold tailWord_5801300
  simp only [CollatzResearch.WordTrace]
  refine ⟨105795396941444179002416677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141060529255258905336555569 105795396941444179002416677)
  ·
    refine ⟨19836636926520783562953127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105795396941444179002416677 19836636926520783562953127)
    ·
      refine ⟨29754955389781175344429691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19836636926520783562953127 29754955389781175344429691)
      ·
        refine ⟨44632433084671763016644537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29754955389781175344429691 44632433084671763016644537)
        ·
          refine ⟨33474324813503822262483403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44632433084671763016644537 33474324813503822262483403)
          ·
            refine ⟨50211487220255733393725105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33474324813503822262483403 50211487220255733393725105)
            ·
              refine ⟨37658615415191800045293829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50211487220255733393725105 37658615415191800045293829)
              ·
                refine ⟨7060990390348462508492593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37658615415191800045293829 7060990390348462508492593)
                ·
                  refine ⟨5295742792761346881369445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7060990390348462508492593 5295742792761346881369445)
                  ·
                    refine ⟨992951773642752540256771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5295742792761346881369445 992951773642752540256771)
                    ·
                      rfl

theorem cell23_5801300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_5801300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5801300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5801300 prefixEnd_5801300 := by exact prefixLift 5801300
  have htrace : WordTrace (prefixWord ++ tailWord_5801300) baseStart_5801300 baseEnd_5801300 := by
    simpa [prefixWord, tailWord_5801300, baseEnd_5801300] using wordTrace_append hprefix tailTrace_5801300
  have hstable : (prefixWord ++ tailWord_5801300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5801300).length < 2 ^ (prefixWord ++ tailWord_5801300).sum := by decide
  have hdescent : baseEnd_5801300 < baseStart_5801300 := by decide
  rcases family_descends (prefixWord ++ tailWord_5801300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5801373 : List Nat := [1, 4, 2, 1, 3, 1, 1, 1, 1, 8]
def baseStart_5801373 : Nat := 118140960795 + 5801373 * 2 ^ 59
def prefixEnd_5801373 : Nat := 4983230072969 + 3 ^ 40 * 5801373 * 2
def baseEnd_5801373 : Nat := 992964268338678611719159

theorem tailTrace_5801373 : CollatzResearch.WordTrace tailWord_5801373 prefixEnd_5801373 992964268338678611719159 := by
  unfold tailWord_5801373
  simp only [CollatzResearch.WordTrace]
  refine ⟨211593456411623891472240773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141062304274415927648160515 211593456411623891472240773)
  ·
    refine ⟨39673773077179479651045145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 211593456411623891472240773 39673773077179479651045145)
    ·
      refine ⟨29755329807884609738283859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39673773077179479651045145 29755329807884609738283859)
      ·
        refine ⟨44632994711826914607425789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29755329807884609738283859 44632994711826914607425789)
        ·
          refine ⟨16737373016935092977784671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44632994711826914607425789 16737373016935092977784671)
          ·
            refine ⟨25106059525402639466677007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16737373016935092977784671 25106059525402639466677007)
            ·
              refine ⟨37659089288103959200015511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25106059525402639466677007 37659089288103959200015511)
              ·
                refine ⟨56488633932155938800023267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37659089288103959200015511 56488633932155938800023267)
                ·
                  refine ⟨84732950898233908200034901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56488633932155938800023267 84732950898233908200034901)
                  ·
                    refine ⟨992964268338678611719159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 84732950898233908200034901 992964268338678611719159)
                    ·
                      rfl

theorem cell23_5801373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_5801373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5801373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5801373 prefixEnd_5801373 := by exact prefixLift 5801373
  have htrace : WordTrace (prefixWord ++ tailWord_5801373) baseStart_5801373 baseEnd_5801373 := by
    simpa [prefixWord, tailWord_5801373, baseEnd_5801373] using wordTrace_append hprefix tailTrace_5801373
  have hstable : (prefixWord ++ tailWord_5801373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5801373).length < 2 ^ (prefixWord ++ tailWord_5801373).sum := by decide
  have hdescent : baseEnd_5801373 < baseStart_5801373 := by decide
  rcases family_descends (prefixWord ++ tailWord_5801373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5801374 : List Nat := [4, 3, 1, 2, 2, 1, 2, 1, 1, 3, 3]
def baseStart_5801374 : Nat := 118140960795 + 5801374 * 2 ^ 59
def prefixEnd_5801374 : Nat := 4983230072969 + 3 ^ 40 * 5801374 * 2
def baseEnd_5801374 : Nat := 2978893318496690331244973

theorem tailTrace_5801374 : CollatzResearch.WordTrace tailWord_5801374 prefixEnd_5801374 2978893318496690331244973 := by
  unfold tailWord_5801374
  simp only [CollatzResearch.WordTrace]
  refine ⟨26449186610577533580378397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141062328589746845762018117 26449186610577533580378397)
  ·
    refine ⟨9918444978966575092641899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26449186610577533580378397 9918444978966575092641899)
    ·
      refine ⟨14877667468449862638962849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9918444978966575092641899 14877667468449862638962849)
      ·
        refine ⟨11158250601337396979222137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14877667468449862638962849 11158250601337396979222137)
        ·
          refine ⟨8368687951003047734416603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11158250601337396979222137 8368687951003047734416603)
          ·
            refine ⟨12553031926504571601624905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8368687951003047734416603 12553031926504571601624905)
            ·
              refine ⟨9414773944878428701218679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12553031926504571601624905 9414773944878428701218679)
              ·
                refine ⟨14122160917317643051828019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9414773944878428701218679 14122160917317643051828019)
                ·
                  refine ⟨21183241375976464577742029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14122160917317643051828019 21183241375976464577742029)
                  ·
                    refine ⟨7943715515991174216653261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21183241375976464577742029 7943715515991174216653261)
                    ·
                      refine ⟨2978893318496690331244973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7943715515991174216653261 2978893318496690331244973)
                      ·
                        rfl

theorem cell23_5801374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_5801374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5801374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5801374 prefixEnd_5801374 := by exact prefixLift 5801374
  have htrace : WordTrace (prefixWord ++ tailWord_5801374) baseStart_5801374 baseEnd_5801374 := by
    simpa [prefixWord, tailWord_5801374, baseEnd_5801374] using wordTrace_append hprefix tailTrace_5801374
  have hstable : (prefixWord ++ tailWord_5801374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5801374).length < 2 ^ (prefixWord ++ tailWord_5801374).sum := by decide
  have hdescent : baseEnd_5801374 < baseStart_5801374 := by decide
  rcases family_descends (prefixWord ++ tailWord_5801374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5801393 : List Nat := [1, 2, 2, 4, 1, 1, 1, 2, 1, 4, 4]
def baseStart_5801393 : Nat := 118140960795 + 5801393 * 2 ^ 59
def prefixEnd_5801393 : Nat := 4983230072969 + 3 ^ 40 * 5801393 * 2
def baseEnd_5801393 : Nat := 2978903074629125756907385

theorem tailTrace_5801393 : CollatzResearch.WordTrace tailWord_5801393 prefixEnd_5801393 2978903074629125756907385 := by
  unfold tailWord_5801393
  simp only [CollatzResearch.WordTrace]
  refine ⟨211594185871551434887968833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141062790581034289925312555 211594185871551434887968833)
  ·
    refine ⟨158695639403663576165976625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211594185871551434887968833 158695639403663576165976625)
    ·
      refine ⟨119021729552747682124482469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158695639403663576165976625 119021729552747682124482469)
      ·
        refine ⟨22316574291140190398340463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119021729552747682124482469 22316574291140190398340463)
        ·
          refine ⟨33474861436710285597510695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22316574291140190398340463 33474861436710285597510695)
          ·
            refine ⟨50212292155065428396266043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33474861436710285597510695 50212292155065428396266043)
            ·
              refine ⟨75318438232598142594399065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50212292155065428396266043 75318438232598142594399065)
              ·
                refine ⟨56488828674448606945799299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75318438232598142594399065 56488828674448606945799299)
                ·
                  refine ⟨84733243011672910418698949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56488828674448606945799299 84733243011672910418698949)
                  ·
                    refine ⟨15887483064688670703506053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 84733243011672910418698949 15887483064688670703506053)
                    ·
                      refine ⟨2978903074629125756907385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15887483064688670703506053 2978903074629125756907385)
                      ·
                        rfl

theorem cell23_5801393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_5801393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5801393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5801393 prefixEnd_5801393 := by exact prefixLift 5801393
  have htrace : WordTrace (prefixWord ++ tailWord_5801393) baseStart_5801393 baseEnd_5801393 := by
    simpa [prefixWord, tailWord_5801393, baseEnd_5801393] using wordTrace_append hprefix tailTrace_5801393
  have hstable : (prefixWord ++ tailWord_5801393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5801393).length < 2 ^ (prefixWord ++ tailWord_5801393).sum := by decide
  have hdescent : baseEnd_5801393 < baseStart_5801393 := by decide
  rcases family_descends (prefixWord ++ tailWord_5801393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5801397 : List Nat := [1, 3, 3, 2, 2, 1, 2, 2, 1, 4, 2]
def baseStart_5801397 : Nat := 118140960795 + 5801397 * 2 ^ 59
def prefixEnd_5801397 : Nat := 4983230072969 + 3 ^ 40 * 5801397 * 2
def baseEnd_5801397 : Nat := 2978905128551743741257367

theorem tailTrace_5801397 : CollatzResearch.WordTrace tailWord_5801397 prefixEnd_5801397 2978905128551743741257367 := by
  unfold tailWord_5801397
  simp only [CollatzResearch.WordTrace]
  refine ⟨211594331763536943571114445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141062887842357962380742963 211594331763536943571114445)
  ·
    refine ⟨79347874411326353839167917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211594331763536943571114445 79347874411326353839167917)
    ·
      refine ⟨29755452904247382689687969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79347874411326353839167917 29755452904247382689687969)
      ·
        refine ⟨22316589678185537017265977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29755452904247382689687969 22316589678185537017265977)
        ·
          refine ⟨16737442258639152762949483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22316589678185537017265977 16737442258639152762949483)
          ·
            refine ⟨25106163387958729144424225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16737442258639152762949483 25106163387958729144424225)
            ·
              refine ⟨18829622540969046858318169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25106163387958729144424225 18829622540969046858318169)
              ·
                refine ⟨14122216905726785143738627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18829622540969046858318169 14122216905726785143738627)
                ·
                  refine ⟨21183325358590177715607941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14122216905726785143738627 21183325358590177715607941)
                  ·
                    refine ⟨3971873504735658321676489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21183325358590177715607941 3971873504735658321676489)
                    ·
                      refine ⟨2978905128551743741257367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3971873504735658321676489 2978905128551743741257367)
                      ·
                        rfl

theorem cell23_5801397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_5801397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5801397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5801397 prefixEnd_5801397 := by exact prefixLift 5801397
  have htrace : WordTrace (prefixWord ++ tailWord_5801397) baseStart_5801397 baseEnd_5801397 := by
    simpa [prefixWord, tailWord_5801397, baseEnd_5801397] using wordTrace_append hprefix tailTrace_5801397
  have hstable : (prefixWord ++ tailWord_5801397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5801397).length < 2 ^ (prefixWord ++ tailWord_5801397).sum := by decide
  have hdescent : baseEnd_5801397 < baseStart_5801397 := by decide
  rcases family_descends (prefixWord ++ tailWord_5801397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5801401 : List Nat := [1, 2, 1, 4, 4, 2, 2, 1, 1, 3, 2]
def baseStart_5801401 : Nat := 118140960795 + 5801401 * 2 ^ 59
def prefixEnd_5801401 : Nat := 4983230072969 + 3 ^ 40 * 5801401 * 2
def baseEnd_5801401 : Nat := 2978907182474361725607349

theorem tailTrace_5801401 : CollatzResearch.WordTrace tailWord_5801401 prefixEnd_5801401 2978907182474361725607349 := by
  unfold tailWord_5801401
  simp only [CollatzResearch.WordTrace]
  refine ⟨211594477655522452254260057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141062985103681634836173371 211594477655522452254260057)
  ·
    refine ⟨158695858241641839190695043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211594477655522452254260057 158695858241641839190695043)
    ·
      refine ⟨238043787362462758786042565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158695858241641839190695043 238043787362462758786042565)
      ·
        refine ⟨44633210130461767272382981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 238043787362462758786042565 44633210130461767272382981)
        ·
          refine ⟨8368726899461581363571809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44633210130461767272382981 8368726899461581363571809)
          ·
            refine ⟨6276545174596186022678857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8368726899461581363571809 6276545174596186022678857)
            ·
              refine ⟨4707408880947139517009143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6276545174596186022678857 4707408880947139517009143)
              ·
                refine ⟨7061113321420709275513715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4707408880947139517009143 7061113321420709275513715)
                ·
                  refine ⟨10591669982131063913270573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7061113321420709275513715 10591669982131063913270573)
                  ·
                    refine ⟨3971876243299148967476465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10591669982131063913270573 3971876243299148967476465)
                    ·
                      refine ⟨2978907182474361725607349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3971876243299148967476465 2978907182474361725607349)
                      ·
                        rfl

theorem cell23_5801401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 1, 1, 3, 2].length) (baseStart_5801401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5801401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5801401 prefixEnd_5801401 := by exact prefixLift 5801401
  have htrace : WordTrace (prefixWord ++ tailWord_5801401) baseStart_5801401 baseEnd_5801401 := by
    simpa [prefixWord, tailWord_5801401, baseEnd_5801401] using wordTrace_append hprefix tailTrace_5801401
  have hstable : (prefixWord ++ tailWord_5801401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5801401).length < 2 ^ (prefixWord ++ tailWord_5801401).sum := by decide
  have hdescent : baseEnd_5801401 < baseStart_5801401 := by decide
  rcases family_descends (prefixWord ++ tailWord_5801401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5801420 : List Nat := [2, 2, 1, 4, 2, 2, 2, 1, 7]
def baseStart_5801420 : Nat := 118140960795 + 5801420 * 2 ^ 59
def prefixEnd_5801420 : Nat := 4983230072969 + 3 ^ 40 * 5801420 * 2
def baseEnd_5801420 : Nat := 330990770956310794585529

theorem tailTrace_5801420 : CollatzResearch.WordTrace tailWord_5801420 prefixEnd_5801420 330990770956310794585529 := by
  unfold tailWord_5801420
  simp only [CollatzResearch.WordTrace]
  refine ⟨105797585321226809249600857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141063447094969078999467809 105797585321226809249600857)
  ·
    refine ⟨79348188990920106937200643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105797585321226809249600857 79348188990920106937200643)
    ·
      refine ⟨119022283486380160405800965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79348188990920106937200643 119022283486380160405800965)
      ·
        refine ⟨22316678153696280076087681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119022283486380160405800965 22316678153696280076087681)
        ·
          refine ⟨16737508615272210057065761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22316678153696280076087681 16737508615272210057065761)
          ·
            refine ⟨12553131461454157542799321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16737508615272210057065761 12553131461454157542799321)
            ·
              refine ⟨9414848596090618157099491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12553131461454157542799321 9414848596090618157099491)
              ·
                refine ⟨14122272894135927235649237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9414848596090618157099491 14122272894135927235649237)
                ·
                  refine ⟨330990770956310794585529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14122272894135927235649237 330990770956310794585529)
                  ·
                    rfl

theorem cell23_5801420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 7].length) (baseStart_5801420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5801420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5801420 prefixEnd_5801420 := by exact prefixLift 5801420
  have htrace : WordTrace (prefixWord ++ tailWord_5801420) baseStart_5801420 baseEnd_5801420 := by
    simpa [prefixWord, tailWord_5801420, baseEnd_5801420] using wordTrace_append hprefix tailTrace_5801420
  have hstable : (prefixWord ++ tailWord_5801420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5801420).length < 2 ^ (prefixWord ++ tailWord_5801420).sum := by decide
  have hdescent : baseEnd_5801420 < baseStart_5801420 := by decide
  rcases family_descends (prefixWord ++ tailWord_5801420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5801433 : List Nat := [1, 2, 1, 2, 4, 2, 1, 2, 1, 7]
def baseStart_5801433 : Nat := 118140960795 + 5801433 * 2 ^ 59
def prefixEnd_5801433 : Nat := 4983230072969 + 3 ^ 40 * 5801433 * 2
def baseEnd_5801433 : Nat := 992974537951768533469067

theorem tailTrace_5801433 : CollatzResearch.WordTrace tailWord_5801433 prefixEnd_5801433 992974537951768533469067 := by
  unfold tailWord_5801433
  simp only [CollatzResearch.WordTrace]
  refine ⟨211595644791406521719424953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141063763194271014479616635 211595644791406521719424953)
  ·
    refine ⟨158696733593554891289568715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211595644791406521719424953 158696733593554891289568715)
    ·
      refine ⟨238045100390332336934353073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158696733593554891289568715 238045100390332336934353073)
      ·
        refine ⟨178533825292749252700764805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238045100390332336934353073 178533825292749252700764805)
        ·
          refine ⟨33475092242390484881393401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 178533825292749252700764805 33475092242390484881393401)
          ·
            refine ⟨25106319181792863661045051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33475092242390484881393401 25106319181792863661045051)
            ·
              refine ⟨37659478772689295491567577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25106319181792863661045051 37659478772689295491567577)
              ·
                refine ⟨28244609079516971618675683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37659478772689295491567577 28244609079516971618675683)
                ·
                  refine ⟨42366913619275457428013525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28244609079516971618675683 42366913619275457428013525)
                  ·
                    refine ⟨992974537951768533469067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42366913619275457428013525 992974537951768533469067)
                    ·
                      rfl

theorem cell23_5801433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 7].length) (baseStart_5801433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5801433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5801433 prefixEnd_5801433 := by exact prefixLift 5801433
  have htrace : WordTrace (prefixWord ++ tailWord_5801433) baseStart_5801433 baseEnd_5801433 := by
    simpa [prefixWord, tailWord_5801433, baseEnd_5801433] using wordTrace_append hprefix tailTrace_5801433
  have hstable : (prefixWord ++ tailWord_5801433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5801433).length < 2 ^ (prefixWord ++ tailWord_5801433).sum := by decide
  have hdescent : baseEnd_5801433 < baseStart_5801433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5801433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5801514 : List Nat := [3, 1, 4, 1, 1, 1, 2, 5, 1, 4]
def baseStart_5801514 : Nat := 118140960795 + 5801514 * 2 ^ 59
def prefixEnd_5801514 : Nat := 4983230072969 + 3 ^ 40 * 5801514 * 2
def baseEnd_5801514 : Nat := 992988401929439927831443

theorem tailTrace_5801514 : CollatzResearch.WordTrace tailWord_5801514 prefixEnd_5801514 992988401929439927831443 := by
  unfold tailWord_5801514
  simp only [CollatzResearch.WordTrace]
  refine ⟨52899649776028268138280899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141065732736075381702082397 52899649776028268138280899)
  ·
    refine ⟨79349474664042402207421349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52899649776028268138280899 79349474664042402207421349)
    ·
      refine ⟨14878026499507950413891503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79349474664042402207421349 14878026499507950413891503)
      ·
        refine ⟨22317039749261925620837255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14878026499507950413891503 22317039749261925620837255)
        ·
          refine ⟨33475559623892888431255883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22317039749261925620837255 33475559623892888431255883)
          ·
            refine ⟨50213339435839332646883825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33475559623892888431255883 50213339435839332646883825)
            ·
              refine ⟨37660004576879499485162869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50213339435839332646883825 37660004576879499485162869)
              ·
                refine ⟨3530625429082453076734019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37660004576879499485162869 3530625429082453076734019)
                ·
                  refine ⟨5295938143623679615101029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3530625429082453076734019 5295938143623679615101029)
                  ·
                    refine ⟨992988401929439927831443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5295938143623679615101029 992988401929439927831443)
                    ·
                      rfl

theorem cell23_5801514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_5801514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5801514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5801514 prefixEnd_5801514 := by exact prefixLift 5801514
  have htrace : WordTrace (prefixWord ++ tailWord_5801514) baseStart_5801514 baseEnd_5801514 := by
    simpa [prefixWord, tailWord_5801514, baseEnd_5801514] using wordTrace_append hprefix tailTrace_5801514
  have hstable : (prefixWord ++ tailWord_5801514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5801514).length < 2 ^ (prefixWord ++ tailWord_5801514).sum := by decide
  have hdescent : baseEnd_5801514 < baseStart_5801514 := by decide
  rcases family_descends (prefixWord ++ tailWord_5801514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5801554 : List Nat := [3, 2, 2, 1, 2, 3, 1, 2, 3, 1, 3]
def baseStart_5801554 : Nat := 118140960795 + 5801554 * 2 ^ 59
def prefixEnd_5801554 : Nat := 4983230072969 + 3 ^ 40 * 5801554 * 2
def baseEnd_5801554 : Nat := 2978985745014499626994145

theorem tailTrace_5801554 : CollatzResearch.WordTrace tailWord_5801554 prefixEnd_5801554 2978985745014499626994145 := by
  unfold tailWord_5801554
  simp only [CollatzResearch.WordTrace]
  refine ⟨52900014505992039846144929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141066705349312106256386477 52900014505992039846144929)
  ·
    refine ⟨39675010879494029884608697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52900014505992039846144929 39675010879494029884608697)
    ·
      refine ⟨29756258159620522413456523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39675010879494029884608697 29756258159620522413456523)
      ·
        refine ⟨44634387239430783620184785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29756258159620522413456523 44634387239430783620184785)
        ·
          refine ⟨33475790429573087715138589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44634387239430783620184785 33475790429573087715138589)
          ·
            refine ⟨12553421411089907893176971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33475790429573087715138589 12553421411089907893176971)
            ·
              refine ⟨18830132116634861839765457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12553421411089907893176971 18830132116634861839765457)
              ·
                refine ⟨14122599087476146379824093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18830132116634861839765457 14122599087476146379824093)
                ·
                  refine ⟨5295974657803554892434035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14122599087476146379824093 5295974657803554892434035)
                  ·
                    refine ⟨7943961986705332338651053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5295974657803554892434035 7943961986705332338651053)
                    ·
                      refine ⟨2978985745014499626994145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7943961986705332338651053 2978985745014499626994145)
                      ·
                        rfl

theorem cell23_5801554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_5801554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5801554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5801554 prefixEnd_5801554 := by exact prefixLift 5801554
  have htrace : WordTrace (prefixWord ++ tailWord_5801554) baseStart_5801554 baseEnd_5801554 := by
    simpa [prefixWord, tailWord_5801554, baseEnd_5801554] using wordTrace_append hprefix tailTrace_5801554
  have hstable : (prefixWord ++ tailWord_5801554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5801554).length < 2 ^ (prefixWord ++ tailWord_5801554).sum := by decide
  have hdescent : baseEnd_5801554 < baseStart_5801554 := by decide
  rcases family_descends (prefixWord ++ tailWord_5801554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5801564 : List Nat := [2, 2, 4, 1, 2, 2, 1, 1, 1, 5, 2]
def baseStart_5801564 : Nat := 118140960795 + 5801564 * 2 ^ 59
def prefixEnd_5801564 : Nat := 4983230072969 + 3 ^ 40 * 5801564 * 2
def baseEnd_5801564 : Nat := 2978990879821044587869099

theorem tailTrace_5801564 : CollatzResearch.WordTrace tailWord_5801564 prefixEnd_5801564 2978990879821044587869099 := by
  unfold tailWord_5801564
  simp only [CollatzResearch.WordTrace]
  refine ⟨105800211376965965546221873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141066948502621287394962497 105800211376965965546221873)
  ·
    refine ⟨79350158532724474159666405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105800211376965965546221873 79350158532724474159666405)
    ·
      refine ⟨14878154724885838904937451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79350158532724474159666405 14878154724885838904937451)
      ·
        refine ⟨22317232087328758357406177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14878154724885838904937451 22317232087328758357406177)
        ·
          refine ⟨16737924065496568768054633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22317232087328758357406177 16737924065496568768054633)
          ·
            refine ⟨12553443049122426576040975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16737924065496568768054633 12553443049122426576040975)
            ·
              refine ⟨18830164573683639864061463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12553443049122426576040975 18830164573683639864061463)
              ·
                refine ⟨28245246860525459796092195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18830164573683639864061463 28245246860525459796092195)
                ·
                  refine ⟨42367870290788189694138293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28245246860525459796092195 42367870290788189694138293)
                  ·
                    refine ⟨3971987839761392783825465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42367870290788189694138293 3971987839761392783825465)
                    ·
                      refine ⟨2978990879821044587869099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3971987839761392783825465 2978990879821044587869099)
                      ·
                        rfl

theorem cell23_5801564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_5801564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5801564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5801564 prefixEnd_5801564 := by exact prefixLift 5801564
  have htrace : WordTrace (prefixWord ++ tailWord_5801564) baseStart_5801564 baseEnd_5801564 := by
    simpa [prefixWord, tailWord_5801564, baseEnd_5801564] using wordTrace_append hprefix tailTrace_5801564
  have hstable : (prefixWord ++ tailWord_5801564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5801564).length < 2 ^ (prefixWord ++ tailWord_5801564).sum := by decide
  have hdescent : baseEnd_5801564 < baseStart_5801564 := by decide
  rcases family_descends (prefixWord ++ tailWord_5801564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5801571 : List Nat := [1, 1, 1, 5, 1, 4, 2, 3, 1, 1, 3]
def baseStart_5801571 : Nat := 118140960795 + 5801571 * 2 ^ 59
def prefixEnd_5801571 : Nat := 4983230072969 + 3 ^ 40 * 5801571 * 2
def baseEnd_5801571 : Nat := 2978994474185626060481567

theorem tailTrace_5801571 : CollatzResearch.WordTrace tailWord_5801571 prefixEnd_5801571 2978994474185626060481567 := by
  unfold tailWord_5801571
  simp only [CollatzResearch.WordTrace]
  refine ⟨211600678064906571287948567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141067118709937714191965711 211600678064906571287948567)
  ·
    refine ⟨317401017097359856931922851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211600678064906571287948567 317401017097359856931922851)
    ·
      refine ⟨476101525646039785397884277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317401017097359856931922851 476101525646039785397884277)
      ·
        refine ⟨44634518029316229881051651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 476101525646039785397884277 44634518029316229881051651)
        ·
          refine ⟨66951777043974344821577477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44634518029316229881051651 66951777043974344821577477)
          ·
            refine ⟨12553458195745189654045777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66951777043974344821577477 12553458195745189654045777)
            ·
              refine ⟨9415093646808892240534333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12553458195745189654045777 9415093646808892240534333)
              ·
                refine ⟨3530660117553334590200375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9415093646808892240534333 3530660117553334590200375)
                ·
                  refine ⟨5295990176330001885300563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3530660117553334590200375 5295990176330001885300563)
                  ·
                    refine ⟨7943985264495002827950845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5295990176330001885300563 7943985264495002827950845)
                    ·
                      refine ⟨2978994474185626060481567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7943985264495002827950845 2978994474185626060481567)
                      ·
                        rfl

theorem cell23_5801571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 3, 1, 1, 3].length) (baseStart_5801571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5801571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5801571 prefixEnd_5801571 := by exact prefixLift 5801571
  have htrace : WordTrace (prefixWord ++ tailWord_5801571) baseStart_5801571 baseEnd_5801571 := by
    simpa [prefixWord, tailWord_5801571, baseEnd_5801571] using wordTrace_append hprefix tailTrace_5801571
  have hstable : (prefixWord ++ tailWord_5801571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5801571).length < 2 ^ (prefixWord ++ tailWord_5801571).sum := by decide
  have hdescent : baseEnd_5801571 < baseStart_5801571 := by decide
  rcases family_descends (prefixWord ++ tailWord_5801571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5801580 : List Nat := [2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 5]
def baseStart_5801580 : Nat := 118140960795 + 5801580 * 2 ^ 59
def prefixEnd_5801580 : Nat := 4983230072969 + 3 ^ 40 * 5801580 * 2
def baseEnd_5801580 : Nat := 2978999095511516525269025

theorem tailTrace_5801580 : CollatzResearch.WordTrace tailWord_5801580 prefixEnd_5801580 2978999095511516525269025 := by
  unfold tailWord_5801580
  simp only [CollatzResearch.WordTrace]
  refine ⟨105800503160936982912513097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141067337547915977216684129 105800503160936982912513097)
  ·
    refine ⟨79350377370702737184384823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105800503160936982912513097 79350377370702737184384823)
    ·
      refine ⟨119025566056054105776577235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79350377370702737184384823 119025566056054105776577235)
      ·
        refine ⟨178538349084081158664865853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119025566056054105776577235 178538349084081158664865853)
        ·
          refine ⟨66951880906530434499324695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178538349084081158664865853 66951880906530434499324695)
          ·
            refine ⟨100427821359795651748987043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66951880906530434499324695 100427821359795651748987043)
            ·
              refine ⟨150641732039693477623480565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100427821359795651748987043 150641732039693477623480565)
              ·
                refine ⟨14122662378721263527201303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 150641732039693477623480565 14122662378721263527201303)
                ·
                  refine ⟨21183993568081895290801955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14122662378721263527201303 21183993568081895290801955)
                  ·
                    refine ⟨31775990352122842936202933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21183993568081895290801955 31775990352122842936202933)
                    ·
                      refine ⟨2978999095511516525269025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31775990352122842936202933 2978999095511516525269025)
                      ·
                        rfl

theorem cell23_5801580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 5].length) (baseStart_5801580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5801580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5801580 prefixEnd_5801580 := by exact prefixLift 5801580
  have htrace : WordTrace (prefixWord ++ tailWord_5801580) baseStart_5801580 baseEnd_5801580 := by
    simpa [prefixWord, tailWord_5801580, baseEnd_5801580] using wordTrace_append hprefix tailTrace_5801580
  have hstable : (prefixWord ++ tailWord_5801580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5801580).length < 2 ^ (prefixWord ++ tailWord_5801580).sum := by decide
  have hdescent : baseEnd_5801580 < baseStart_5801580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5801580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5801597 : List Nat := [1, 4, 1, 1, 4, 2, 1, 2, 1, 1, 5]
def baseStart_5801597 : Nat := 118140960795 + 5801597 * 2 ^ 59
def prefixEnd_5801597 : Nat := 4983230072969 + 3 ^ 40 * 5801597 * 2
def baseEnd_5801597 : Nat := 2979007824682642958756447

theorem tailTrace_5801597 : CollatzResearch.WordTrace tailWord_5801597 prefixEnd_5801597 2979007824682642958756447 := by
  unfold tailWord_5801597
  simp only [CollatzResearch.WordTrace]
  refine ⟨211601626362812377728395045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141067750908541585152263363 211601626362812377728395045)
  ·
    refine ⟨39675304943027320824074071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 211601626362812377728395045 39675304943027320824074071)
    ·
      refine ⟨59512957414540981236111107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39675304943027320824074071 59512957414540981236111107)
      ·
        refine ⟨89269436121811471854166661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59512957414540981236111107 89269436121811471854166661)
        ·
          refine ⟨16738019272839650972656249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89269436121811471854166661 16738019272839650972656249)
          ·
            refine ⟨12553514454629738229492187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16738019272839650972656249 12553514454629738229492187)
            ·
              refine ⟨18830271681944607344238281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12553514454629738229492187 18830271681944607344238281)
              ·
                refine ⟨14122703761458455508178711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18830271681944607344238281 14122703761458455508178711)
                ·
                  refine ⟨21184055642187683262268067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14122703761458455508178711 21184055642187683262268067)
                  ·
                    refine ⟨31776083463281524893402101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21184055642187683262268067 31776083463281524893402101)
                    ·
                      refine ⟨2979007824682642958756447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31776083463281524893402101 2979007824682642958756447)
                      ·
                        rfl

theorem cell23_5801597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_5801597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5801597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5801597 prefixEnd_5801597 := by exact prefixLift 5801597
  have htrace : WordTrace (prefixWord ++ tailWord_5801597) baseStart_5801597 baseEnd_5801597 := by
    simpa [prefixWord, tailWord_5801597, baseEnd_5801597] using wordTrace_append hprefix tailTrace_5801597
  have hstable : (prefixWord ++ tailWord_5801597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5801597).length < 2 ^ (prefixWord ++ tailWord_5801597).sum := by decide
  have hdescent : baseEnd_5801597 < baseStart_5801597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5801597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5801604 : List Nat := [2, 3, 2, 1, 4, 2, 1, 1, 1, 6]
def baseStart_5801604 : Nat := 118140960795 + 5801604 * 2 ^ 59
def prefixEnd_5801604 : Nat := 4983230072969 + 3 ^ 40 * 5801604 * 2
def baseEnd_5801604 : Nat := 993003806349074810456305

theorem tailTrace_5801604 : CollatzResearch.WordTrace tailWord_5801604 prefixEnd_5801604 993003806349074810456305 := by
  unfold tailWord_5801604
  simp only [CollatzResearch.WordTrace]
  refine ⟨105800940836893508961949933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141067921115858011949266577 105800940836893508961949933)
  ·
    refine ⟨39675352813835065860731225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105800940836893508961949933 39675352813835065860731225)
    ·
      refine ⟨29756514610376299395548419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39675352813835065860731225 29756514610376299395548419)
      ·
        refine ⟨44634771915564449093322629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29756514610376299395548419 44634771915564449093322629)
        ·
          refine ⟨8369019734168334204997993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44634771915564449093322629 8369019734168334204997993)
          ·
            refine ⟨6276764800626250653748495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8369019734168334204997993 6276764800626250653748495)
            ·
              refine ⟨9415147200939375980622743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6276764800626250653748495 9415147200939375980622743)
              ·
                refine ⟨14122720801409063970934115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9415147200939375980622743 14122720801409063970934115)
                ·
                  refine ⟨21184081202113595956401173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14122720801409063970934115 21184081202113595956401173)
                  ·
                    refine ⟨993003806349074810456305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21184081202113595956401173 993003806349074810456305)
                    ·
                      rfl

theorem cell23_5801604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_5801604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5801604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5801604 prefixEnd_5801604 := by exact prefixLift 5801604
  have htrace : WordTrace (prefixWord ++ tailWord_5801604) baseStart_5801604 baseEnd_5801604 := by
    simpa [prefixWord, tailWord_5801604, baseEnd_5801604] using wordTrace_append hprefix tailTrace_5801604
  have hstable : (prefixWord ++ tailWord_5801604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5801604).length < 2 ^ (prefixWord ++ tailWord_5801604).sum := by decide
  have hdescent : baseEnd_5801604 < baseStart_5801604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5801604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5801607 : List Nat := [1, 1, 4, 2, 1, 3, 3, 1, 1, 2, 4]
def baseStart_5801607 : Nat := 118140960795 + 5801607 * 2 ^ 59
def prefixEnd_5801607 : Nat := 4983230072969 + 3 ^ 40 * 5801607 * 2
def baseEnd_5801607 : Nat := 2979012959489187919631401

theorem tailTrace_5801607 : CollatzResearch.WordTrace tailWord_5801607 prefixEnd_5801607 2979012959489187919631401 := by
  unfold tailWord_5801607
  simp only [CollatzResearch.WordTrace]
  refine ⟨211601991092776149436259075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141067994061850766290839383 211601991092776149436259075)
  ·
    refine ⟨317402986639164224154388613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211601991092776149436259075 317402986639164224154388613)
    ·
      refine ⟨59513059994843292028947865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 317402986639164224154388613 59513059994843292028947865)
      ·
        refine ⟨44634794996132469021710899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59513059994843292028947865 44634794996132469021710899)
        ·
          refine ⟨66952192494198703532566349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44634794996132469021710899 66952192494198703532566349)
          ·
            refine ⟨25107072185324513824712381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66952192494198703532566349 25107072185324513824712381)
            ·
              refine ⟨9415152069496692684267143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25107072185324513824712381 9415152069496692684267143)
              ·
                refine ⟨14122728104245039026400715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9415152069496692684267143 14122728104245039026400715)
                ·
                  refine ⟨21184092156367558539601073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14122728104245039026400715 21184092156367558539601073)
                  ·
                    refine ⟨15888069117275668904700805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21184092156367558539601073 15888069117275668904700805)
                    ·
                      refine ⟨2979012959489187919631401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15888069117275668904700805 2979012959489187919631401)
                      ·
                        rfl

theorem cell23_5801607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_5801607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5801607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5801607 prefixEnd_5801607 := by exact prefixLift 5801607
  have htrace : WordTrace (prefixWord ++ tailWord_5801607) baseStart_5801607 baseEnd_5801607 := by
    simpa [prefixWord, tailWord_5801607, baseEnd_5801607] using wordTrace_append hprefix tailTrace_5801607
  have hstable : (prefixWord ++ tailWord_5801607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5801607).length < 2 ^ (prefixWord ++ tailWord_5801607).sum := by decide
  have hdescent : baseEnd_5801607 < baseStart_5801607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5801607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5801614 : List Nat := [4, 1, 1, 3, 1, 2, 1, 4, 1, 2, 3]
def baseStart_5801614 : Nat := 118140960795 + 5801614 * 2 ^ 59
def prefixEnd_5801614 : Nat := 4983230072969 + 3 ^ 40 * 5801614 * 2
def baseEnd_5801614 : Nat := 2979016553853769392243869

theorem tailTrace_5801614 : CollatzResearch.WordTrace tailWord_5801614 prefixEnd_5801614 2979016553853769392243869 := by
  unfold tailWord_5801614
  simp only [CollatzResearch.WordTrace]
  refine ⟨26450280800468848703970487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141068164269167193087842597 26450280800468848703970487)
  ·
    refine ⟨39675421200703273055955731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26450280800468848703970487 39675421200703273055955731)
    ·
      refine ⟨59513131801054909583933597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39675421200703273055955731 59513131801054909583933597)
      ·
        refine ⟨22317424425395591093975099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59513131801054909583933597 22317424425395591093975099)
        ·
          refine ⟨33476136638093386640962649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22317424425395591093975099 33476136638093386640962649)
          ·
            refine ⟨25107102478570039980721987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33476136638093386640962649 25107102478570039980721987)
            ·
              refine ⟨37660653717855059971082981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25107102478570039980721987 37660653717855059971082981)
              ·
                refine ⟨7061372572097823744578059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37660653717855059971082981 7061372572097823744578059)
                ·
                  refine ⟨10592058858146735616867089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7061372572097823744578059 10592058858146735616867089)
                  ·
                    refine ⟨7944044143610051712650317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10592058858146735616867089 7944044143610051712650317)
                    ·
                      refine ⟨2979016553853769392243869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7944044143610051712650317 2979016553853769392243869)
                      ·
                        rfl

theorem cell23_5801614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_5801614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5801614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5801614 prefixEnd_5801614 := by exact prefixLift 5801614
  have htrace : WordTrace (prefixWord ++ tailWord_5801614) baseStart_5801614 baseEnd_5801614 := by
    simpa [prefixWord, tailWord_5801614, baseEnd_5801614] using wordTrace_append hprefix tailTrace_5801614
  have hstable : (prefixWord ++ tailWord_5801614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5801614).length < 2 ^ (prefixWord ++ tailWord_5801614).sum := by decide
  have hdescent : baseEnd_5801614 < baseStart_5801614 := by decide
  rcases family_descends (prefixWord ++ tailWord_5801614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5801634 : List Nat := [3, 3, 1, 4, 1, 2, 9]
def baseStart_5801634 : Nat := 118140960795 + 5801634 * 2 ^ 59
def prefixEnd_5801634 : Nat := 4983230072969 + 3 ^ 40 * 5801634 * 2
def baseEnd_5801634 : Nat := 36778108931689621160417

theorem tailTrace_5801634 : CollatzResearch.WordTrace tailWord_5801634 prefixEnd_5801634 36778108931689621160417 := by
  unfold tailWord_5801634
  simp only [CollatzResearch.WordTrace]
  refine ⟨52900743965919583261872989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141068650575785555364994637 52900743965919583261872989)
  ·
    refine ⟨19837778987219843723202371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52900743965919583261872989 19837778987219843723202371)
    ·
      refine ⟨29756668480829765584803557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19837778987219843723202371 29756668480829765584803557)
      ·
        refine ⟨5579375340155581047150667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29756668480829765584803557 5579375340155581047150667)
        ·
          refine ⟨8369063010233371570726001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5579375340155581047150667 8369063010233371570726001)
          ·
            refine ⟨6276797257675028678044501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8369063010233371570726001 6276797257675028678044501)
            ·
              refine ⟨36778108931689621160417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6276797257675028678044501 36778108931689621160417)
              ·
                rfl

theorem cell23_5801634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 9].length) (baseStart_5801634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5801634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5801634 prefixEnd_5801634 := by exact prefixLift 5801634
  have htrace : WordTrace (prefixWord ++ tailWord_5801634) baseStart_5801634 baseEnd_5801634 := by
    simpa [prefixWord, tailWord_5801634, baseEnd_5801634] using wordTrace_append hprefix tailTrace_5801634
  have hstable : (prefixWord ++ tailWord_5801634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5801634).length < 2 ^ (prefixWord ++ tailWord_5801634).sum := by decide
  have hdescent : baseEnd_5801634 < baseStart_5801634 := by decide
  rcases family_descends (prefixWord ++ tailWord_5801634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5801645 : List Nat := [1, 5, 2, 1, 1, 1, 5, 2, 1, 2, 2]
def baseStart_5801645 : Nat := 118140960795 + 5801645 * 2 ^ 59
def prefixEnd_5801645 : Nat := 4983230072969 + 3 ^ 40 * 5801645 * 2
def baseEnd_5801645 : Nat := 2979032471754058770956227

theorem tailTrace_5801645 : CollatzResearch.WordTrace tailWord_5801645 prefixEnd_5801645 2979032471754058770956227 := by
  unfold tailWord_5801645
  simp only [CollatzResearch.WordTrace]
  refine ⟨211603377066638481926142389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141068918044425654617428259 211603377066638481926142389)
  ·
    refine ⟨19837816599997357680575849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 211603377066638481926142389 19837816599997357680575849)
    ·
      refine ⟨14878362449998018260431887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19837816599997357680575849 14878362449998018260431887)
      ·
        refine ⟨22317543674997027390647831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14878362449998018260431887 22317543674997027390647831)
        ·
          refine ⟨33476315512495541085971747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22317543674997027390647831 33476315512495541085971747)
          ·
            refine ⟨50214473268743311628957621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33476315512495541085971747 50214473268743311628957621)
            ·
              refine ⟨4707606868944685465214777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50214473268743311628957621 4707606868944685465214777)
              ·
                refine ⟨3530705151708514098911083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4707606868944685465214777 3530705151708514098911083)
                ·
                  refine ⟨5296057727562771148366625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3530705151708514098911083 5296057727562771148366625)
                  ·
                    refine ⟨3972043295672078361274969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5296057727562771148366625 3972043295672078361274969)
                    ·
                      refine ⟨2979032471754058770956227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3972043295672078361274969 2979032471754058770956227)
                      ·
                        rfl

theorem cell23_5801645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_5801645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5801645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5801645 prefixEnd_5801645 := by exact prefixLift 5801645
  have htrace : WordTrace (prefixWord ++ tailWord_5801645) baseStart_5801645 baseEnd_5801645 := by
    simpa [prefixWord, tailWord_5801645, baseEnd_5801645] using wordTrace_append hprefix tailTrace_5801645
  have hstable : (prefixWord ++ tailWord_5801645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5801645).length < 2 ^ (prefixWord ++ tailWord_5801645).sum := by decide
  have hdescent : baseEnd_5801645 < baseStart_5801645 := by decide
  rcases family_descends (prefixWord ++ tailWord_5801645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5801667 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 7, 4, 2]
def baseStart_5801667 : Nat := 118140960795 + 5801667 * 2 ^ 59
def prefixEnd_5801667 : Nat := 4983230072969 + 3 ^ 40 * 5801667 * 2
def baseEnd_5801667 : Nat := 2979043768328457684881125

theorem tailTrace_5801667 : CollatzResearch.WordTrace tailWord_5801667 prefixEnd_5801667 2979043768328457684881125 := by
  unfold tailWord_5801667
  simp only [CollatzResearch.WordTrace]
  refine ⟨211604179472558779683443255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141069452981705853122295503 211604179472558779683443255)
  ·
    refine ⟨317406269208838169525164883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211604179472558779683443255 317406269208838169525164883)
    ·
      refine ⟨476109403813257254287747325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317406269208838169525164883 476109403813257254287747325)
      ·
        refine ⟨178541026429971470357905247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 476109403813257254287747325 178541026429971470357905247)
        ·
          refine ⟨267811539644957205536857871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178541026429971470357905247 267811539644957205536857871)
          ·
            refine ⟨401717309467435808305286807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267811539644957205536857871 401717309467435808305286807)
            ·
              refine ⟨602575964201153712457930211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 401717309467435808305286807 602575964201153712457930211)
              ·
                refine ⟨903863946301730568686895317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 602575964201153712457930211 903863946301730568686895317)
                ·
                  refine ⟨21184311241446810203599109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 903863946301730568686895317 21184311241446810203599109)
                  ·
                    refine ⟨3972058357771276913174833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21184311241446810203599109 3972058357771276913174833)
                    ·
                      refine ⟨2979043768328457684881125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3972058357771276913174833 2979043768328457684881125)
                      ·
                        rfl

theorem cell23_5801667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 4, 2].length) (baseStart_5801667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5801667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5801667 prefixEnd_5801667 := by exact prefixLift 5801667
  have htrace : WordTrace (prefixWord ++ tailWord_5801667) baseStart_5801667 baseEnd_5801667 := by
    simpa [prefixWord, tailWord_5801667, baseEnd_5801667] using wordTrace_append hprefix tailTrace_5801667
  have hstable : (prefixWord ++ tailWord_5801667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5801667).length < 2 ^ (prefixWord ++ tailWord_5801667).sum := by decide
  have hdescent : baseEnd_5801667 < baseStart_5801667 := by decide
  rcases family_descends (prefixWord ++ tailWord_5801667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5801680 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 4]
def baseStart_5801680 : Nat := 118140960795 + 5801680 * 2 ^ 59
def prefixEnd_5801680 : Nat := 4983230072969 + 3 ^ 40 * 5801680 * 2
def baseEnd_5801680 : Nat := 2979050443576966134018565

theorem tailTrace_5801680 : CollatzResearch.WordTrace tailWord_5801680 prefixEnd_5801680 2979050443576966134018565 := by
  unfold tailWord_5801680
  simp only [CollatzResearch.WordTrace]
  refine ⟨105802326810755841451833247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141069769081007788602444329 105802326810755841451833247)
  ·
    refine ⟨158703490216133762177749871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105802326810755841451833247 158703490216133762177749871)
    ·
      refine ⟨238055235324200643266624807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158703490216133762177749871 238055235324200643266624807)
      ·
        refine ⟨357082852986300964899937211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238055235324200643266624807 357082852986300964899937211)
        ·
          refine ⟨535624279479451447349905817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357082852986300964899937211 535624279479451447349905817)
          ·
            refine ⟨401718209609588585512429363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 535624279479451447349905817 401718209609588585512429363)
            ·
              refine ⟨602577314414382878268644045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 401718209609588585512429363 602577314414382878268644045)
              ·
                refine ⟨225966492905393579350741517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 602577314414382878268644045 225966492905393579350741517)
                ·
                  refine ⟨84737434839522592256528069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 225966492905393579350741517 84737434839522592256528069)
                  ·
                    refine ⟨15888269032410486048099013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 84737434839522592256528069 15888269032410486048099013)
                    ·
                      refine ⟨2979050443576966134018565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15888269032410486048099013 2979050443576966134018565)
                      ·
                        rfl

theorem cell23_5801680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 4].length) (baseStart_5801680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5801680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5801680 prefixEnd_5801680 := by exact prefixLift 5801680
  have htrace : WordTrace (prefixWord ++ tailWord_5801680) baseStart_5801680 baseEnd_5801680 := by
    simpa [prefixWord, tailWord_5801680, baseEnd_5801680] using wordTrace_append hprefix tailTrace_5801680
  have hstable : (prefixWord ++ tailWord_5801680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5801680).length < 2 ^ (prefixWord ++ tailWord_5801680).sum := by decide
  have hdescent : baseEnd_5801680 < baseStart_5801680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5801680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5801718 : List Nat := [5, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2]
def baseStart_5801718 : Nat := 118140960795 + 5801718 * 2 ^ 59
def prefixEnd_5801718 : Nat := 4983230072969 + 3 ^ 40 * 5801718 * 2
def baseEnd_5801718 : Nat := 2979069955841836985343391

theorem tailTrace_5801718 : CollatzResearch.WordTrace tailWord_5801718 prefixEnd_5801718 2979069955841836985343391 := by
  unfold tailWord_5801718
  simp only [CollatzResearch.WordTrace]
  refine ⟨13225377474710875962096863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141070693063582676929033205 13225377474710875962096863)
  ·
    refine ⟨19838066212066313943145295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13225377474710875962096863 19838066212066313943145295)
    ·
      refine ⟨29757099318099470914717943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19838066212066313943145295 29757099318099470914717943)
      ·
        refine ⟨44635648977149206372076915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29757099318099470914717943 44635648977149206372076915)
        ·
          refine ⟨66953473465723809558115373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44635648977149206372076915 66953473465723809558115373)
          ·
            refine ⟨25107552549646428584293265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66953473465723809558115373 25107552549646428584293265)
            ·
              refine ⟨18830664412234821438219949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25107552549646428584293265 18830664412234821438219949)
              ·
                refine ⟨7061499154588058039332481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18830664412234821438219949 7061499154588058039332481)
                ·
                  refine ⟨5296124365941043529499361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7061499154588058039332481 5296124365941043529499361)
                  ·
                    refine ⟨3972093274455782647124521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5296124365941043529499361 3972093274455782647124521)
                    ·
                      refine ⟨2979069955841836985343391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3972093274455782647124521 2979069955841836985343391)
                      ·
                        rfl

theorem cell23_5801718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2].length) (baseStart_5801718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5801718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5801718 prefixEnd_5801718 := by exact prefixLift 5801718
  have htrace : WordTrace (prefixWord ++ tailWord_5801718) baseStart_5801718 baseEnd_5801718 := by
    simpa [prefixWord, tailWord_5801718, baseEnd_5801718] using wordTrace_append hprefix tailTrace_5801718
  have hstable : (prefixWord ++ tailWord_5801718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5801718).length < 2 ^ (prefixWord ++ tailWord_5801718).sum := by decide
  have hdescent : baseEnd_5801718 < baseStart_5801718 := by decide
  rcases family_descends (prefixWord ++ tailWord_5801718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5801758 : List Nat := [4, 3, 2, 2, 1, 1, 2, 1, 7]
def baseStart_5801758 : Nat := 118140960795 + 5801758 * 2 ^ 59
def prefixEnd_5801758 : Nat := 4983230072969 + 3 ^ 40 * 5801758 * 2
def baseEnd_5801758 : Nat := 331010055007557425427023

theorem tailTrace_5801758 : CollatzResearch.WordTrace tailWord_5801758 prefixEnd_5801758 331010055007557425427023 := by
  unfold tailWord_5801758
  simp only [CollatzResearch.WordTrace]
  refine ⟨26450937314403637778125741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141071665676819401483337285 26450937314403637778125741)
  ·
    refine ⟨9919101492901364166797153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26450937314403637778125741 9919101492901364166797153)
    ·
      refine ⟨7439326119676023125097865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9919101492901364166797153 7439326119676023125097865)
      ·
        refine ⟨5579494589757017343823399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7439326119676023125097865 5579494589757017343823399)
        ·
          refine ⟨8369241884635526015735099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5579494589757017343823399 8369241884635526015735099)
          ·
            refine ⟨12553862826953289023602649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8369241884635526015735099 12553862826953289023602649)
            ·
              refine ⟨9415397120214966767701987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12553862826953289023602649 9415397120214966767701987)
              ·
                refine ⟨14123095680322450151552981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9415397120214966767701987 14123095680322450151552981)
                ·
                  refine ⟨331010055007557425427023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14123095680322450151552981 331010055007557425427023)
                  ·
                    rfl

theorem cell23_5801758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_5801758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5801758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5801758 prefixEnd_5801758 := by exact prefixLift 5801758
  have htrace : WordTrace (prefixWord ++ tailWord_5801758) baseStart_5801758 baseEnd_5801758 := by
    simpa [prefixWord, tailWord_5801758, baseEnd_5801758] using wordTrace_append hprefix tailTrace_5801758
  have hstable : (prefixWord ++ tailWord_5801758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5801758).length < 2 ^ (prefixWord ++ tailWord_5801758).sum := by decide
  have hdescent : baseEnd_5801758 < baseStart_5801758 := by decide
  rcases family_descends (prefixWord ++ tailWord_5801758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5801784 : List Nat := [2, 1, 2, 1, 3, 3, 2, 2, 3, 4]
def baseStart_5801784 : Nat := 118140960795 + 5801784 * 2 ^ 59
def prefixEnd_5801784 : Nat := 4983230072969 + 3 ^ 40 * 5801784 * 2
def baseEnd_5801784 : Nat := 993034615188344575706029

theorem tailTrace_5801784 : CollatzResearch.WordTrace tailWord_5801784 prefixEnd_5801784 993034615188344575706029 := by
  unfold tailWord_5801784
  simp only [CollatzResearch.WordTrace]
  refine ⟨105804223406567454332726203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141072297875423272443634937 105804223406567454332726203)
  ·
    refine ⟨158706335109851181499089305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105804223406567454332726203 158706335109851181499089305)
    ·
      refine ⟨119029751332388386124316979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158706335109851181499089305 119029751332388386124316979)
      ·
        refine ⟨178544626998582579186475469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119029751332388386124316979 178544626998582579186475469)
        ·
          refine ⟨66954235124468467194928301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178544626998582579186475469 66954235124468467194928301)
          ·
            refine ⟨25107838171675675198098113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66954235124468467194928301 25107838171675675198098113)
            ·
              refine ⟨18830878628756756398573585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25107838171675675198098113 18830878628756756398573585)
              ·
                refine ⟨14123158971567567298930189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18830878628756756398573585 14123158971567567298930189)
                ·
                  refine ⟨5296184614337837737098821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14123158971567567298930189 5296184614337837737098821)
                  ·
                    refine ⟨993034615188344575706029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5296184614337837737098821 993034615188344575706029)
                    ·
                      rfl

theorem cell23_5801784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 3, 4].length) (baseStart_5801784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5801784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5801784 prefixEnd_5801784 := by exact prefixLift 5801784
  have htrace : WordTrace (prefixWord ++ tailWord_5801784) baseStart_5801784 baseEnd_5801784 := by
    simpa [prefixWord, tailWord_5801784, baseEnd_5801784] using wordTrace_append hprefix tailTrace_5801784
  have hstable : (prefixWord ++ tailWord_5801784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5801784).length < 2 ^ (prefixWord ++ tailWord_5801784).sum := by decide
  have hdescent : baseEnd_5801784 < baseStart_5801784 := by decide
  rcases family_descends (prefixWord ++ tailWord_5801784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5801818 : List Nat := [3, 1, 1, 2, 1, 3, 5, 2, 1, 4]
def baseStart_5801818 : Nat := 118140960795 + 5801818 * 2 ^ 59
def prefixEnd_5801818 : Nat := 4983230072969 + 3 ^ 40 * 5801818 * 2
def baseEnd_5801818 : Nat := 993040434635762198030977

theorem tailTrace_5801818 : CollatzResearch.WordTrace tailWord_5801818 prefixEnd_5801818 993040434635762198030977 := by
  unfold tailWord_5801818
  simp only [CollatzResearch.WordTrace]
  refine ⟨52902421723752933118047527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141073124596674488314793405 52902421723752933118047527)
  ·
    refine ⟨79353632585629399677071291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52902421723752933118047527 79353632585629399677071291)
    ·
      refine ⟨119030448878444099515606937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79353632585629399677071291 119030448878444099515606937)
      ·
        refine ⟨89272836658833074636705203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119030448878444099515606937 89272836658833074636705203)
        ·
          refine ⟨133909254988249611955057805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89272836658833074636705203 133909254988249611955057805)
          ·
            refine ⟨50215970620593604483146677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133909254988249611955057805 50215970620593604483146677)
            ·
              refine ⟨4707747245680650420295001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50215970620593604483146677 4707747245680650420295001)
              ·
                refine ⟨3530810434260487815221251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4707747245680650420295001 3530810434260487815221251)
                ·
                  refine ⟨5296215651390731722831877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3530810434260487815221251 5296215651390731722831877)
                  ·
                    refine ⟨993040434635762198030977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5296215651390731722831877 993040434635762198030977)
                    ·
                      rfl

theorem cell23_5801818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 2, 1, 4].length) (baseStart_5801818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5801818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5801818 prefixEnd_5801818 := by exact prefixLift 5801818
  have htrace : WordTrace (prefixWord ++ tailWord_5801818) baseStart_5801818 baseEnd_5801818 := by
    simpa [prefixWord, tailWord_5801818, baseEnd_5801818] using wordTrace_append hprefix tailTrace_5801818
  have hstable : (prefixWord ++ tailWord_5801818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5801818).length < 2 ^ (prefixWord ++ tailWord_5801818).sum := by decide
  have hdescent : baseEnd_5801818 < baseStart_5801818 := by decide
  rcases family_descends (prefixWord ++ tailWord_5801818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5801861 : List Nat := [1, 3, 1, 1, 3, 2, 5, 1, 1, 5]
def baseStart_5801861 : Nat := 118140960795 + 5801861 * 2 ^ 59
def prefixEnd_5801861 : Nat := 4983230072969 + 3 ^ 40 * 5801861 * 2
def baseEnd_5801861 : Nat := 993047794525143308618411

theorem tailTrace_5801861 : CollatzResearch.WordTrace tailWord_5801861 prefixEnd_5801861 993047794525143308618411 := by
  unfold tailWord_5801861
  simp only [CollatzResearch.WordTrace]
  refine ⟨211611255233855950816005437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141074170155903967210670291 211611255233855950816005437)
  ·
    refine ⟨79354220712695981556002039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211611255233855950816005437 79354220712695981556002039)
    ·
      refine ⟨119031331069043972334003059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79354220712695981556002039 119031331069043972334003059)
      ·
        refine ⟨178546996603565958501004589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119031331069043972334003059 178546996603565958501004589)
        ·
          refine ⟨66955123726337234437876721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178546996603565958501004589 66955123726337234437876721)
          ·
            refine ⟨50216342794752925828407541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66955123726337234437876721 50216342794752925828407541)
            ·
              refine ⟨4707782137008086796413207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50216342794752925828407541 4707782137008086796413207)
              ·
                refine ⟨7061673205512130194619811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4707782137008086796413207 7061673205512130194619811)
                ·
                  refine ⟨10592509808268195291929717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7061673205512130194619811 10592509808268195291929717)
                  ·
                    refine ⟨993047794525143308618411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10592509808268195291929717 993047794525143308618411)
                    ·
                      rfl

theorem cell23_5801861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 1, 1, 5].length) (baseStart_5801861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5801861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5801861 prefixEnd_5801861 := by exact prefixLift 5801861
  have htrace : WordTrace (prefixWord ++ tailWord_5801861) baseStart_5801861 baseEnd_5801861 := by
    simpa [prefixWord, tailWord_5801861, baseEnd_5801861] using wordTrace_append hprefix tailTrace_5801861
  have hstable : (prefixWord ++ tailWord_5801861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5801861).length < 2 ^ (prefixWord ++ tailWord_5801861).sum := by decide
  have hdescent : baseEnd_5801861 < baseStart_5801861 := by decide
  rcases family_descends (prefixWord ++ tailWord_5801861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5801902 : List Nat := [4, 1, 5, 1, 1, 1, 1, 1, 1, 5, 2]
def baseStart_5801902 : Nat := 118140960795 + 5801902 * 2 ^ 59
def prefixEnd_5801902 : Nat := 4983230072969 + 3 ^ 40 * 5801902 * 2
def baseEnd_5801902 : Nat := 2979164436282264265442545

theorem tailTrace_5801902 : CollatzResearch.WordTrace tailWord_5801902 prefixEnd_5801902 2979164436282264265442545 := by
  unfold tailWord_5801902
  simp only [CollatzResearch.WordTrace]
  refine ⟨26451593828338426852280995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141075167084471609878831973 26451593828338426852280995)
  ·
    refine ⟨39677390742507640278421493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26451593828338426852280995 39677390742507640278421493)
    ·
      refine ⟨3719755382110091276102015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39677390742507640278421493 3719755382110091276102015)
      ·
        refine ⟨5579633073165136914153023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3719755382110091276102015 5579633073165136914153023)
        ·
          refine ⟨8369449609747705371229535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5579633073165136914153023 8369449609747705371229535)
          ·
            refine ⟨12554174414621558056844303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8369449609747705371229535 12554174414621558056844303)
            ·
              refine ⟨18831261621932337085266455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12554174414621558056844303 18831261621932337085266455)
              ·
                refine ⟨28246892432898505627899683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18831261621932337085266455 28246892432898505627899683)
                ·
                  refine ⟨42370338649347758441849525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28246892432898505627899683 42370338649347758441849525)
                  ·
                    refine ⟨3972219248376352353923393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42370338649347758441849525 3972219248376352353923393)
                    ·
                      refine ⟨2979164436282264265442545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3972219248376352353923393 2979164436282264265442545)
                      ·
                        rfl

theorem cell23_5801902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_5801902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5801902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5801902 prefixEnd_5801902 := by exact prefixLift 5801902
  have htrace : WordTrace (prefixWord ++ tailWord_5801902) baseStart_5801902 baseEnd_5801902 := by
    simpa [prefixWord, tailWord_5801902, baseEnd_5801902] using wordTrace_append hprefix tailTrace_5801902
  have hstable : (prefixWord ++ tailWord_5801902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5801902).length < 2 ^ (prefixWord ++ tailWord_5801902).sum := by decide
  have hdescent : baseEnd_5801902 < baseStart_5801902 := by decide
  rcases family_descends (prefixWord ++ tailWord_5801902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5801914 : List Nat := [3, 1, 1, 1, 2, 1, 2, 3, 3, 3, 3]
def baseStart_5801914 : Nat := 118140960795 + 5801914 * 2 ^ 59
def prefixEnd_5801914 : Nat := 4983230072969 + 3 ^ 40 * 5801914 * 2
def baseEnd_5801914 : Nat := 2979170598050118218492489

theorem tailTrace_5801914 : CollatzResearch.WordTrace tailWord_5801914 prefixEnd_5801914 2979170598050118218492489 := by
  unfold tailWord_5801914
  simp only [CollatzResearch.WordTrace]
  refine ⟨52903297075665985216921199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141075458868442627245123197 52903297075665985216921199)
  ·
    refine ⟨79354945613498977825381799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52903297075665985216921199 79354945613498977825381799)
    ·
      refine ⟨119032418420248466738072699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79354945613498977825381799 119032418420248466738072699)
      ·
        refine ⟨178548627630372700107109049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119032418420248466738072699 178548627630372700107109049)
        ·
          refine ⟨133911470722779525080331787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178548627630372700107109049 133911470722779525080331787)
          ·
            refine ⟨200867206084169287620497681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133911470722779525080331787 200867206084169287620497681)
            ·
              refine ⟨150650404563126965715373261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200867206084169287620497681 150650404563126965715373261)
              ·
                refine ⟨56493901711172612143264973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150650404563126965715373261 56493901711172612143264973)
                ·
                  refine ⟨21185213141689729553724365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56493901711172612143264973 21185213141689729553724365)
                  ·
                    refine ⟨7944454928133648582646637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21185213141689729553724365 7944454928133648582646637)
                    ·
                      refine ⟨2979170598050118218492489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7944454928133648582646637 2979170598050118218492489)
                      ·
                        rfl

theorem cell23_5801914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 3, 3, 3].length) (baseStart_5801914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5801914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5801914 prefixEnd_5801914 := by exact prefixLift 5801914
  have htrace : WordTrace (prefixWord ++ tailWord_5801914) baseStart_5801914 baseEnd_5801914 := by
    simpa [prefixWord, tailWord_5801914, baseEnd_5801914] using wordTrace_append hprefix tailTrace_5801914
  have hstable : (prefixWord ++ tailWord_5801914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5801914).length < 2 ^ (prefixWord ++ tailWord_5801914).sum := by decide
  have hdescent : baseEnd_5801914 < baseStart_5801914 := by decide
  rcases family_descends (prefixWord ++ tailWord_5801914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5801918 : List Nat := [4, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3]
def baseStart_5801918 : Nat := 118140960795 + 5801918 * 2 ^ 59
def prefixEnd_5801918 : Nat := 4983230072969 + 3 ^ 40 * 5801918 * 2
def baseEnd_5801918 : Nat := 2979172651972736202842471

theorem tailTrace_5801918 : CollatzResearch.WordTrace tailWord_5801918 prefixEnd_5801918 2979172651972736202842471 := by
  unfold tailWord_5801918
  simp only [CollatzResearch.WordTrace]
  refine ⟨26451666774331181193853801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141075556129766299700553605 26451666774331181193853801)
  ·
    refine ⟨19838750080748385895390351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26451666774331181193853801 19838750080748385895390351)
    ·
      refine ⟨29758125121122578843085527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19838750080748385895390351 29758125121122578843085527)
      ·
        refine ⟨44637187681683868264628291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29758125121122578843085527 44637187681683868264628291)
        ·
          refine ⟨66955781522525802396942437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44637187681683868264628291 66955781522525802396942437)
          ·
            refine ⟨12554209035473587949426707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66955781522525802396942437 12554209035473587949426707)
            ·
              refine ⟨18831313553210381924140061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12554209035473587949426707 18831313553210381924140061)
              ·
                refine ⟨7061742582453893221552523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18831313553210381924140061 7061742582453893221552523)
                ·
                  refine ⟨10592613873680839832328785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7061742582453893221552523 10592613873680839832328785)
                  ·
                    refine ⟨7944460405260629874246589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10592613873680839832328785 7944460405260629874246589)
                    ·
                      refine ⟨2979172651972736202842471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7944460405260629874246589 2979172651972736202842471)
                      ·
                        rfl

theorem cell23_5801918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_5801918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5801918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5801918 prefixEnd_5801918 := by exact prefixLift 5801918
  have htrace : WordTrace (prefixWord ++ tailWord_5801918) baseStart_5801918 baseEnd_5801918 := by
    simpa [prefixWord, tailWord_5801918, baseEnd_5801918] using wordTrace_append hprefix tailTrace_5801918
  have hstable : (prefixWord ++ tailWord_5801918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5801918).length < 2 ^ (prefixWord ++ tailWord_5801918).sum := by decide
  have hdescent : baseEnd_5801918 < baseStart_5801918 := by decide
  rcases family_descends (prefixWord ++ tailWord_5801918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5801931 : List Nat := [1, 1, 1, 1, 3, 4, 3, 1, 4, 1, 3]
def baseStart_5801931 : Nat := 118140960795 + 5801931 * 2 ^ 59
def prefixEnd_5801931 : Nat := 4983230072969 + 3 ^ 40 * 5801931 * 2
def baseEnd_5801931 : Nat := 2979179327221244651979911

theorem tailTrace_5801931 : CollatzResearch.WordTrace tailWord_5801931 prefixEnd_5801931 2979179327221244651979911 := by
  unfold tailWord_5801931
  simp only [CollatzResearch.WordTrace]
  refine ⟨211613808343602352771053647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141075872229068235180702431 211613808343602352771053647)
  ·
    refine ⟨317420712515403529156580471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211613808343602352771053647 317420712515403529156580471)
    ·
      refine ⟨476131068773105293734870707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317420712515403529156580471 476131068773105293734870707)
      ·
        refine ⟨714196603159657940602306061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 476131068773105293734870707 714196603159657940602306061)
        ·
          refine ⟨267823726184871727725864773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 714196603159657940602306061 267823726184871727725864773)
          ·
            refine ⟨50216948659663448948599645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 267823726184871727725864773 50216948659663448948599645)
            ·
              refine ⟨18831355747373793355724867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50216948659663448948599645 18831355747373793355724867)
              ·
                refine ⟨28247033621060690033587301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18831355747373793355724867 28247033621060690033587301)
                ·
                  refine ⟨5296318803948879381297619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28247033621060690033587301 5296318803948879381297619)
                  ·
                    refine ⟨7944478205923319071946429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5296318803948879381297619 7944478205923319071946429)
                    ·
                      refine ⟨2979179327221244651979911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7944478205923319071946429 2979179327221244651979911)
                      ·
                        rfl

theorem cell23_5801931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 4, 1, 3].length) (baseStart_5801931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5801931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5801931 prefixEnd_5801931 := by exact prefixLift 5801931
  have htrace : WordTrace (prefixWord ++ tailWord_5801931) baseStart_5801931 baseEnd_5801931 := by
    simpa [prefixWord, tailWord_5801931, baseEnd_5801931] using wordTrace_append hprefix tailTrace_5801931
  have hstable : (prefixWord ++ tailWord_5801931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5801931).length < 2 ^ (prefixWord ++ tailWord_5801931).sum := by decide
  have hdescent : baseEnd_5801931 < baseStart_5801931 := by decide
  rcases family_descends (prefixWord ++ tailWord_5801931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5801942 : List Nat := [5, 2, 1, 1, 3, 1, 3, 1, 2, 4]
def baseStart_5801942 : Nat := 118140960795 + 5801942 * 2 ^ 59
def prefixEnd_5801942 : Nat := 4983230072969 + 3 ^ 40 * 5801942 * 2
def baseEnd_5801942 : Nat := 993061658502814702980787

theorem tailTrace_5801942 : CollatzResearch.WordTrace tailWord_5801942 prefixEnd_5801942 993061658502814702980787 := by
  unfold tailWord_5801942
  simp only [CollatzResearch.WordTrace]
  refine ⟨13225888096660156353106505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141076139697708334433136053 13225888096660156353106505)
  ·
    refine ⟨9919416072495117264829879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13225888096660156353106505 9919416072495117264829879)
    ·
      refine ⟨14879124108742675897244819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9919416072495117264829879 14879124108742675897244819)
      ·
        refine ⟨22318686163114013845867229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14879124108742675897244819 22318686163114013845867229)
        ·
          refine ⟨8369507311167755192200211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22318686163114013845867229 8369507311167755192200211)
          ·
            refine ⟨12554260966751632788300317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8369507311167755192200211 12554260966751632788300317)
            ·
              refine ⟨4707847862531862295612619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12554260966751632788300317 4707847862531862295612619)
              ·
                refine ⟨7061771793797793443418929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4707847862531862295612619 7061771793797793443418929)
                ·
                  refine ⟨5296328845348345082564197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7061771793797793443418929 5296328845348345082564197)
                  ·
                    refine ⟨993061658502814702980787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5296328845348345082564197 993061658502814702980787)
                    ·
                      rfl

theorem cell23_5801942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_5801942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5801942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5801942 prefixEnd_5801942 := by exact prefixLift 5801942
  have htrace : WordTrace (prefixWord ++ tailWord_5801942) baseStart_5801942 baseEnd_5801942 := by
    simpa [prefixWord, tailWord_5801942, baseEnd_5801942] using wordTrace_append hprefix tailTrace_5801942
  have hstable : (prefixWord ++ tailWord_5801942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5801942).length < 2 ^ (prefixWord ++ tailWord_5801942).sum := by decide
  have hdescent : baseEnd_5801942 < baseStart_5801942 := by decide
  rcases family_descends (prefixWord ++ tailWord_5801942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5801971 : List Nat := [1, 1, 1, 2, 2, 2, 1, 6, 1, 4, 2]
def baseStart_5801971 : Nat := 118140960795 + 5801971 * 2 ^ 59
def prefixEnd_5801971 : Nat := 4983230072969 + 3 ^ 40 * 5801971 * 2
def baseEnd_5801971 : Nat := 2979199866447424495479727

theorem tailTrace_5801971 : CollatzResearch.WordTrace tailWord_5801971 prefixEnd_5801971 2979199866447424495479727 := by
  unfold tailWord_5801971
  simp only [CollatzResearch.WordTrace]
  refine ⟨211615267263457439602509767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141076844842304959735006511 211615267263457439602509767)
  ·
    refine ⟨317422900895186159403764651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211615267263457439602509767 317422900895186159403764651)
    ·
      refine ⟨476134351342779239105646977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317422900895186159403764651 476134351342779239105646977)
      ·
        refine ⟨357100763507084429329235233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 476134351342779239105646977 357100763507084429329235233)
        ·
          refine ⟨267825572630313321996926425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 357100763507084429329235233 267825572630313321996926425)
          ·
            refine ⟨200869179472734991497694819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267825572630313321996926425 200869179472734991497694819)
            ·
              refine ⟨301303769209102487246542229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200869179472734991497694819 301303769209102487246542229)
              ·
                refine ⟨14123614181676679089681667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 301303769209102487246542229 14123614181676679089681667)
                ·
                  refine ⟨21185421272515018634522501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14123614181676679089681667 21185421272515018634522501)
                  ·
                    refine ⟨3972266488596565993972969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21185421272515018634522501 3972266488596565993972969)
                    ·
                      refine ⟨2979199866447424495479727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3972266488596565993972969 2979199866447424495479727)
                      ·
                        rfl

theorem cell23_5801971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 4, 2].length) (baseStart_5801971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5801971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5801971 prefixEnd_5801971 := by exact prefixLift 5801971
  have htrace : WordTrace (prefixWord ++ tailWord_5801971) baseStart_5801971 baseEnd_5801971 := by
    simpa [prefixWord, tailWord_5801971, baseEnd_5801971] using wordTrace_append hprefix tailTrace_5801971
  have hstable : (prefixWord ++ tailWord_5801971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5801971).length < 2 ^ (prefixWord ++ tailWord_5801971).sum := by decide
  have hdescent : baseEnd_5801971 < baseStart_5801971 := by decide
  rcases family_descends (prefixWord ++ tailWord_5801971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5801984 : List Nat := [2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 4]
def baseStart_5801984 : Nat := 118140960795 + 5801984 * 2 ^ 59
def prefixEnd_5801984 : Nat := 4983230072969 + 3 ^ 40 * 5801984 * 2
def baseEnd_5801984 : Nat := 2979206541695932944617167

theorem tailTrace_5801984 : CollatzResearch.WordTrace tailWord_5801984 prefixEnd_5801984 2979206541695932944617167 := by
  unfold tailWord_5801984
  simp only [CollatzResearch.WordTrace]
  refine ⟨105807870706205171411366503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141077160941606895215155337 105807870706205171411366503)
  ·
    refine ⟨158711806059307757117049755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105807870706205171411366503 158711806059307757117049755)
    ·
      refine ⟨238067709088961635675574633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158711806059307757117049755 238067709088961635675574633)
      ·
        refine ⟨178550781816721226756680975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238067709088961635675574633 178550781816721226756680975)
        ·
          refine ⟨267826172725081840135021463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178550781816721226756680975 267826172725081840135021463)
          ·
            refine ⟨401739259087622760202532195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267826172725081840135021463 401739259087622760202532195)
            ·
              refine ⟨602608888631434140303798293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 401739259087622760202532195 602608888631434140303798293)
              ·
                refine ⟨28247291654598475326740545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 602608888631434140303798293 28247291654598475326740545)
                ·
                  refine ⟨21185468740948856495055409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28247291654598475326740545 21185468740948856495055409)
                  ·
                    refine ⟨15889101555711642371291557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21185468740948856495055409 15889101555711642371291557)
                    ·
                      refine ⟨2979206541695932944617167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15889101555711642371291557 2979206541695932944617167)
                      ·
                        rfl

theorem cell23_5801984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 4].length) (baseStart_5801984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5801984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5801984 prefixEnd_5801984 := by exact prefixLift 5801984
  have htrace : WordTrace (prefixWord ++ tailWord_5801984) baseStart_5801984 baseEnd_5801984 := by
    simpa [prefixWord, tailWord_5801984, baseEnd_5801984] using wordTrace_append hprefix tailTrace_5801984
  have hstable : (prefixWord ++ tailWord_5801984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5801984).length < 2 ^ (prefixWord ++ tailWord_5801984).sum := by decide
  have hdescent : baseEnd_5801984 < baseStart_5801984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5801984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5802038 : List Nat := [5, 1, 2, 1, 1, 1, 2, 2, 2, 3, 3]
def baseStart_5802038 : Nat := 118140960795 + 5802038 * 2 ^ 59
def prefixEnd_5802038 : Nat := 4983230072969 + 3 ^ 40 * 5802038 * 2
def baseEnd_5802038 : Nat := 2979234269651275733341919

theorem tailTrace_5802038 : CollatzResearch.WordTrace tailWord_5802038 prefixEnd_5802038 2979234269651275733341919 := by
  unfold tailWord_5802038
  simp only [CollatzResearch.WordTrace]
  refine ⟨13226106934638419377824923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141078473969476473363465845 13226106934638419377824923)
  ·
    refine ⟨19839160401957629066737385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13226106934638419377824923 19839160401957629066737385)
    ·
      refine ⟨14879370301468221800053039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19839160401957629066737385 14879370301468221800053039)
      ·
        refine ⟨22319055452202332700079559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14879370301468221800053039 22319055452202332700079559)
        ·
          refine ⟨33478583178303499050119339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22319055452202332700079559 33478583178303499050119339)
          ·
            refine ⟨50217874767455248575179009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33478583178303499050119339 50217874767455248575179009)
            ·
              refine ⟨37663406075591436431384257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50217874767455248575179009 37663406075591436431384257)
              ·
                refine ⟨28247554556693577323538193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37663406075591436431384257 28247554556693577323538193)
                ·
                  refine ⟨21185665917520182992653645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28247554556693577323538193 21185665917520182992653645)
                  ·
                    refine ⟨7944624719070068622245117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21185665917520182992653645 7944624719070068622245117)
                    ·
                      refine ⟨2979234269651275733341919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7944624719070068622245117 2979234269651275733341919)
                      ·
                        rfl

theorem cell23_5802038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_5802038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5802038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5802038 prefixEnd_5802038 := by exact prefixLift 5802038
  have htrace : WordTrace (prefixWord ++ tailWord_5802038) baseStart_5802038 baseEnd_5802038 := by
    simpa [prefixWord, tailWord_5802038, baseEnd_5802038] using wordTrace_append hprefix tailTrace_5802038
  have hstable : (prefixWord ++ tailWord_5802038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5802038).length < 2 ^ (prefixWord ++ tailWord_5802038).sum := by decide
  have hdescent : baseEnd_5802038 < baseStart_5802038 := by decide
  rcases family_descends (prefixWord ++ tailWord_5802038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5802071 : List Nat := [1, 1, 3, 2, 2, 1, 3, 1, 5, 4]
def baseStart_5802071 : Nat := 118140960795 + 5802071 * 2 ^ 59
def prefixEnd_5802071 : Nat := 4983230072969 + 3 ^ 40 * 5802071 * 2
def baseEnd_5802071 : Nat := 993083738170958034743089

theorem tailTrace_5802071 : CollatzResearch.WordTrace tailWord_5802071 prefixEnd_5802071 993083738170958034743089 := by
  unfold tailWord_5802071
  simp only [CollatzResearch.WordTrace]
  refine ⟨211618914563095156681150067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141079276375396771120766711 211618914563095156681150067)
  ·
    refine ⟨317428371844642735021725101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211618914563095156681150067 317428371844642735021725101)
    ·
      refine ⟨119035639441741025633146913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 317428371844642735021725101 119035639441741025633146913)
      ·
        refine ⟨89276729581305769224860185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119035639441741025633146913 89276729581305769224860185)
        ·
          refine ⟨66957547185979326918645139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89276729581305769224860185 66957547185979326918645139)
          ·
            refine ⟨100436320778968990377967709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66957547185979326918645139 100436320778968990377967709)
            ·
              refine ⟨37663620292113371391737891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100436320778968990377967709 37663620292113371391737891)
              ·
                refine ⟨56495430438170057087606837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37663620292113371391737891 56495430438170057087606837)
                ·
                  refine ⟨5296446603578442851963141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56495430438170057087606837 5296446603578442851963141)
                  ·
                    refine ⟨993083738170958034743089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5296446603578442851963141 993083738170958034743089)
                    ·
                      rfl

theorem cell23_5802071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 5, 4].length) (baseStart_5802071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5802071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5802071 prefixEnd_5802071 := by exact prefixLift 5802071
  have htrace : WordTrace (prefixWord ++ tailWord_5802071) baseStart_5802071 baseEnd_5802071 := by
    simpa [prefixWord, tailWord_5802071, baseEnd_5802071] using wordTrace_append hprefix tailTrace_5802071
  have hstable : (prefixWord ++ tailWord_5802071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5802071).length < 2 ^ (prefixWord ++ tailWord_5802071).sum := by decide
  have hdescent : baseEnd_5802071 < baseStart_5802071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5802071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5802105 : List Nat := [1, 2, 1, 3, 4, 1, 2, 4, 1, 4]
def baseStart_5802105 : Nat := 118140960795 + 5802105 * 2 ^ 59
def prefixEnd_5802105 : Nat := 4983230072969 + 3 ^ 40 * 5802105 * 2
def baseEnd_5802105 : Nat := 993089557618375657068037

theorem tailTrace_5802105 : CollatzResearch.WordTrace tailWord_5802105 prefixEnd_5802105 993089557618375657068037 := by
  unfold tailWord_5802105
  simp only [CollatzResearch.WordTrace]
  refine ⟨211620154644971980487887769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141080103096647986991925179 211620154644971980487887769)
  ·
    refine ⟨158715115983728985365915827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211620154644971980487887769 158715115983728985365915827)
    ·
      refine ⟨238072673975593478048873741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158715115983728985365915827 238072673975593478048873741)
      ·
        refine ⟨89277252740847554268327653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238072673975593478048873741 89277252740847554268327653)
        ·
          refine ⟨16739484888908916425311435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89277252740847554268327653 16739484888908916425311435)
          ·
            refine ⟨25109227333363374637967153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16739484888908916425311435 25109227333363374637967153)
            ·
              refine ⟨18831920500022530978475365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25109227333363374637967153 18831920500022530978475365)
              ·
                refine ⟨3530985093754224558464131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18831920500022530978475365 3530985093754224558464131)
                ·
                  refine ⟨5296477640631336837696197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3530985093754224558464131 5296477640631336837696197)
                  ·
                    refine ⟨993089557618375657068037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5296477640631336837696197 993089557618375657068037)
                    ·
                      rfl

theorem cell23_5802105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 4, 1, 4].length) (baseStart_5802105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5802105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5802105 prefixEnd_5802105 := by exact prefixLift 5802105
  have htrace : WordTrace (prefixWord ++ tailWord_5802105) baseStart_5802105 baseEnd_5802105 := by
    simpa [prefixWord, tailWord_5802105, baseEnd_5802105] using wordTrace_append hprefix tailTrace_5802105
  have hstable : (prefixWord ++ tailWord_5802105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5802105).length < 2 ^ (prefixWord ++ tailWord_5802105).sum := by decide
  have hdescent : baseEnd_5802105 < baseStart_5802105 := by decide
  rcases family_descends (prefixWord ++ tailWord_5802105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5802128 : List Nat := [2, 1, 1, 1, 1, 1, 5, 4, 3, 1, 3]
def baseStart_5802128 : Nat := 118140960795 + 5802128 * 2 ^ 59
def prefixEnd_5802128 : Nat := 4983230072969 + 3 ^ 40 * 5802128 * 2
def baseEnd_5802128 : Nat := 2979280482910180381216505

theorem tailTrace_5802128 : CollatzResearch.WordTrace tailWord_5802128 prefixEnd_5802128 2979280482910180381216505 := by
  unfold tailWord_5802128
  simp only [CollatzResearch.WordTrace]
  refine ⟨105810496761944327707987519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141080662349259103610650025 105810496761944327707987519)
  ·
    refine ⟨158715745142916491561981279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105810496761944327707987519 158715745142916491561981279)
    ·
      refine ⟨238073617714374737342971919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158715745142916491561981279 238073617714374737342971919)
      ·
        refine ⟨357110426571562106014457879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238073617714374737342971919 357110426571562106014457879)
        ·
          refine ⟨535665639857343159021686819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357110426571562106014457879 535665639857343159021686819)
          ·
            refine ⟨803498459786014738532530229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 535665639857343159021686819 803498459786014738532530229)
            ·
              refine ⟨75327980604938881737424709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 803498459786014738532530229 75327980604938881737424709)
              ·
                refine ⟨14123996363426040325767133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75327980604938881737424709 14123996363426040325767133)
                ·
                  refine ⟨5296498636284765122162675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14123996363426040325767133 5296498636284765122162675)
                  ·
                    refine ⟨7944747954427147683244013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5296498636284765122162675 7944747954427147683244013)
                    ·
                      refine ⟨2979280482910180381216505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7944747954427147683244013 2979280482910180381216505)
                      ·
                        rfl

theorem cell23_5802128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 3, 1, 3].length) (baseStart_5802128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5802128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5802128 prefixEnd_5802128 := by exact prefixLift 5802128
  have htrace : WordTrace (prefixWord ++ tailWord_5802128) baseStart_5802128 baseEnd_5802128 := by
    simpa [prefixWord, tailWord_5802128, baseEnd_5802128] using wordTrace_append hprefix tailTrace_5802128
  have hstable : (prefixWord ++ tailWord_5802128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5802128).length < 2 ^ (prefixWord ++ tailWord_5802128).sum := by decide
  have hdescent : baseEnd_5802128 < baseStart_5802128 := by decide
  rcases family_descends (prefixWord ++ tailWord_5802128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5802171 : List Nat := [1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 5]
def baseStart_5802171 : Nat := 118140960795 + 5802171 * 2 ^ 59
def prefixEnd_5802171 : Nat := 4983230072969 + 3 ^ 40 * 5802171 * 2
def baseEnd_5802171 : Nat := 2979302562578323712978807

theorem tailTrace_5802171 : CollatzResearch.WordTrace tailWord_5802171 prefixEnd_5802171 2979302562578323712978807 := by
  unfold tailWord_5802171
  simp only [CollatzResearch.WordTrace]
  refine ⟨211622561862732873759790367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141081707908488582506526911 211622561862732873759790367)
  ·
    refine ⟨317433842794099310639685551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211622561862732873759790367 317433842794099310639685551)
    ·
      refine ⟨476150764191148965959528327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317433842794099310639685551 476150764191148965959528327)
      ·
        refine ⟨714226146286723448939292491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 476150764191148965959528327 714226146286723448939292491)
        ·
          refine ⟨1071339219430085173408938737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 714226146286723448939292491 1071339219430085173408938737)
          ·
            refine ⟨803504414572563880056704053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1071339219430085173408938737 803504414572563880056704053)
            ·
              refine ⟨75328538866177863755316005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 803504414572563880056704053 75328538866177863755316005)
              ·
                refine ⟨14124101037408349454121751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75328538866177863755316005 14124101037408349454121751)
                ·
                  refine ⟨21186151556112524181182627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14124101037408349454121751 21186151556112524181182627)
                  ·
                    refine ⟨31779227334168786271773941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21186151556112524181182627 31779227334168786271773941)
                    ·
                      refine ⟨2979302562578323712978807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31779227334168786271773941 2979302562578323712978807)
                      ·
                        rfl

theorem cell23_5802171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 5].length) (baseStart_5802171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5802171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5802171 prefixEnd_5802171 := by exact prefixLift 5802171
  have htrace : WordTrace (prefixWord ++ tailWord_5802171) baseStart_5802171 baseEnd_5802171 := by
    simpa [prefixWord, tailWord_5802171, baseEnd_5802171] using wordTrace_append hprefix tailTrace_5802171
  have hstable : (prefixWord ++ tailWord_5802171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5802171).length < 2 ^ (prefixWord ++ tailWord_5802171).sum := by decide
  have hdescent : baseEnd_5802171 < baseStart_5802171 := by decide
  rcases family_descends (prefixWord ++ tailWord_5802171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5802181 : List Nat := [1, 3, 1, 1, 1, 1, 6, 1, 1, 1, 6]
def baseStart_5802181 : Nat := 118140960795 + 5802181 * 2 ^ 59
def prefixEnd_5802181 : Nat := 4983230072969 + 3 ^ 40 * 5802181 * 2
def baseEnd_5802181 : Nat := 2979307697384868673853761

theorem tailTrace_5802181 : CollatzResearch.WordTrace tailWord_5802181 prefixEnd_5802181 2979307697384868673853761 := by
  unfold tailWord_5802181
  simp only [CollatzResearch.WordTrace]
  refine ⟨211622926592696645467654397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141081951061797763645102931 211622926592696645467654397)
  ·
    refine ⟨79358597472261242050370399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211622926592696645467654397 79358597472261242050370399)
    ·
      refine ⟨119037896208391863075555599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79358597472261242050370399 119037896208391863075555599)
      ·
        refine ⟨178556844312587794613333399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119037896208391863075555599 178556844312587794613333399)
        ·
          refine ⟨267835266468881691920000099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178556844312587794613333399 267835266468881691920000099)
          ·
            refine ⟨401752899703322537880000149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267835266468881691920000099 401752899703322537880000149)
            ·
              refine ⟨18832167173593243963125007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 401752899703322537880000149 18832167173593243963125007)
              ·
                refine ⟨28248250760389865944687511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18832167173593243963125007 28248250760389865944687511)
                ·
                  refine ⟨42372376140584798917031267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28248250760389865944687511 42372376140584798917031267)
                  ·
                    refine ⟨63558564210877198375546901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42372376140584798917031267 63558564210877198375546901)
                    ·
                      refine ⟨2979307697384868673853761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63558564210877198375546901 2979307697384868673853761)
                      ·
                        rfl

theorem cell23_5802181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 1, 6].length) (baseStart_5802181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5802181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5802181 prefixEnd_5802181 := by exact prefixLift 5802181
  have htrace : WordTrace (prefixWord ++ tailWord_5802181) baseStart_5802181 baseEnd_5802181 := by
    simpa [prefixWord, tailWord_5802181, baseEnd_5802181] using wordTrace_append hprefix tailTrace_5802181
  have hstable : (prefixWord ++ tailWord_5802181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5802181).length < 2 ^ (prefixWord ++ tailWord_5802181).sum := by decide
  have hdescent : baseEnd_5802181 < baseStart_5802181 := by decide
  rcases family_descends (prefixWord ++ tailWord_5802181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5802205 : List Nat := [1, 4, 3, 2, 1, 1, 3, 1, 1, 1, 5]
def baseStart_5802205 : Nat := 118140960795 + 5802205 * 2 ^ 59
def prefixEnd_5802205 : Nat := 4983230072969 + 3 ^ 40 * 5802205 * 2
def baseEnd_5802205 : Nat := 2979320020920576579953651

theorem tailTrace_5802205 : CollatzResearch.WordTrace tailWord_5802205 prefixEnd_5802205 2979320020920576579953651 := by
  unfold tailWord_5802205
  simp only [CollatzResearch.WordTrace]
  refine ⟨211623801944609697566528069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141082534629739798377685379 211623801944609697566528069)
  ·
    refine ⟨39679462864614318293724013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 211623801944609697566528069 39679462864614318293724013)
    ·
      refine ⟨14879798574230369360146505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39679462864614318293724013 14879798574230369360146505)
      ·
        refine ⟨11159848930672777020109879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14879798574230369360146505 11159848930672777020109879)
        ·
          refine ⟨16739773396009165530164819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11159848930672777020109879 16739773396009165530164819)
          ·
            refine ⟨25109660094013748295247229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16739773396009165530164819 25109660094013748295247229)
            ·
              refine ⟨9416122535255155610717711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25109660094013748295247229 9416122535255155610717711)
              ·
                refine ⟨14124183802882733416076567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9416122535255155610717711 14124183802882733416076567)
                ·
                  refine ⟨21186275704324100124114851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14124183802882733416076567 21186275704324100124114851)
                  ·
                    refine ⟨31779413556486150186172277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21186275704324100124114851 31779413556486150186172277)
                    ·
                      refine ⟨2979320020920576579953651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31779413556486150186172277 2979320020920576579953651)
                      ·
                        rfl

theorem cell23_5802205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_5802205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5802205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5802205 prefixEnd_5802205 := by exact prefixLift 5802205
  have htrace : WordTrace (prefixWord ++ tailWord_5802205) baseStart_5802205 baseEnd_5802205 := by
    simpa [prefixWord, tailWord_5802205, baseEnd_5802205] using wordTrace_append hprefix tailTrace_5802205
  have hstable : (prefixWord ++ tailWord_5802205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5802205).length < 2 ^ (prefixWord ++ tailWord_5802205).sum := by decide
  have hdescent : baseEnd_5802205 < baseStart_5802205 := by decide
  rcases family_descends (prefixWord ++ tailWord_5802205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5802218 : List Nat := [3, 1, 3, 1, 1, 2, 1, 2, 3, 3, 3]
def baseStart_5802218 : Nat := 118140960795 + 5802218 * 2 ^ 59
def prefixEnd_5802218 : Nat := 4983230072969 + 3 ^ 40 * 5802218 * 2
def baseEnd_5802218 : Nat := 2979326696169085029091091

theorem tailTrace_5802218 : CollatzResearch.WordTrace tailWord_5802218 prefixEnd_5802218 2979326696169085029091091 := by
  unfold tailWord_5802218
  simp only [CollatzResearch.WordTrace]
  refine ⟨52906069023390650196687827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141082850729041733857834205 52906069023390650196687827)
  ·
    refine ⟨79359103535085975295031741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52906069023390650196687827 79359103535085975295031741)
    ·
      refine ⟨29759663825657240735636903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79359103535085975295031741 29759663825657240735636903)
      ·
        refine ⟨44639495738485861103455355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29759663825657240735636903 44639495738485861103455355)
        ·
          refine ⟨66959243607728791655183033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44639495738485861103455355 66959243607728791655183033)
          ·
            refine ⟨50219432705796593741387275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66959243607728791655183033 50219432705796593741387275)
            ·
              refine ⟨75329149058694890612080913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50219432705796593741387275 75329149058694890612080913)
              ·
                refine ⟨56496861794021167959060685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75329149058694890612080913 56496861794021167959060685)
                ·
                  refine ⟨21186323172757937984647757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56496861794021167959060685 21186323172757937984647757)
                  ·
                    refine ⟨7944871189784226744242909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21186323172757937984647757 7944871189784226744242909)
                    ·
                      refine ⟨2979326696169085029091091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7944871189784226744242909 2979326696169085029091091)
                      ·
                        rfl

theorem cell23_5802218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_5802218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5802218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5802218 prefixEnd_5802218 := by exact prefixLift 5802218
  have htrace : WordTrace (prefixWord ++ tailWord_5802218) baseStart_5802218 baseEnd_5802218 := by
    simpa [prefixWord, tailWord_5802218, baseEnd_5802218] using wordTrace_append hprefix tailTrace_5802218
  have hstable : (prefixWord ++ tailWord_5802218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5802218).length < 2 ^ (prefixWord ++ tailWord_5802218).sum := by decide
  have hdescent : baseEnd_5802218 < baseStart_5802218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5802218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5802238 : List Nat := [4, 2, 2, 1, 1, 1, 1, 2, 2, 7]
def baseStart_5802238 : Nat := 118140960795 + 5802238 * 2 ^ 59
def prefixEnd_5802238 : Nat := 4983230072969 + 3 ^ 40 * 5802238 * 2
def baseEnd_5802238 : Nat := 993112321927391650280333

theorem tailTrace_5802238 : CollatzResearch.WordTrace tailWord_5802238 prefixEnd_5802238 993112321927391650280333 := by
  unfold tailWord_5802238
  simp only [CollatzResearch.WordTrace]
  refine ⟨26453125694186268025309921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141083337035660096134986245 26453125694186268025309921)
  ·
    refine ⟨19839844270639701018982441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26453125694186268025309921 19839844270639701018982441)
    ·
      refine ⟨14879883202979775764236831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19839844270639701018982441 14879883202979775764236831)
      ·
        refine ⟨22319824804469663646355247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14879883202979775764236831 22319824804469663646355247)
        ·
          refine ⟨33479737206704495469532871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22319824804469663646355247 33479737206704495469532871)
          ·
            refine ⟨50219605810056743204299307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33479737206704495469532871 50219605810056743204299307)
            ·
              refine ⟨75329408715085114806448961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50219605810056743204299307 75329408715085114806448961)
              ·
                refine ⟨56497056536313836104836721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75329408715085114806448961 56497056536313836104836721)
                ·
                  refine ⟨42372792402235377078627541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56497056536313836104836721 42372792402235377078627541)
                  ·
                    refine ⟨993112321927391650280333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42372792402235377078627541 993112321927391650280333)
                    ·
                      rfl

theorem cell23_5802238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_5802238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5802238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5802238 prefixEnd_5802238 := by exact prefixLift 5802238
  have htrace : WordTrace (prefixWord ++ tailWord_5802238) baseStart_5802238 baseEnd_5802238 := by
    simpa [prefixWord, tailWord_5802238, baseEnd_5802238] using wordTrace_append hprefix tailTrace_5802238
  have hstable : (prefixWord ++ tailWord_5802238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5802238).length < 2 ^ (prefixWord ++ tailWord_5802238).sum := by decide
  have hdescent : baseEnd_5802238 < baseStart_5802238 := by decide
  rcases family_descends (prefixWord ++ tailWord_5802238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5802251 : List Nat := [1, 1, 1, 1, 5, 2, 1, 2, 1, 8]
def baseStart_5802251 : Nat := 118140960795 + 5802251 * 2 ^ 59
def prefixEnd_5802251 : Nat := 4983230072969 + 3 ^ 40 * 5802251 * 2
def baseEnd_5802251 : Nat := 993114547010227799992813

theorem tailTrace_5802251 : CollatzResearch.WordTrace tailWord_5802251 prefixEnd_5802251 993114547010227799992813 := by
  unfold tailWord_5802251
  simp only [CollatzResearch.WordTrace]
  refine ⟨211625479702443047422702607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141083653134962031615135071 211625479702443047422702607)
  ·
    refine ⟨317438219553664571134053911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211625479702443047422702607 317438219553664571134053911)
    ·
      refine ⟨476157329330496856701080867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317438219553664571134053911 476157329330496856701080867)
      ·
        refine ⟨714235993995745285051621301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 476157329330496856701080867 714235993995745285051621301)
        ·
          refine ⟨66959624437101120473589497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 714235993995745285051621301 66959624437101120473589497)
          ·
            refine ⟨50219718327825840355192123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66959624437101120473589497 50219718327825840355192123)
            ·
              refine ⟨75329577491738760532788185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50219718327825840355192123 75329577491738760532788185)
              ·
                refine ⟨56497183118804070399591139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75329577491738760532788185 56497183118804070399591139)
                ·
                  refine ⟨84745774678206105599386709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56497183118804070399591139 84745774678206105599386709)
                  ·
                    refine ⟨993114547010227799992813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 84745774678206105599386709 993114547010227799992813)
                    ·
                      rfl

theorem cell23_5802251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 8].length) (baseStart_5802251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5802251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5802251 prefixEnd_5802251 := by exact prefixLift 5802251
  have htrace : WordTrace (prefixWord ++ tailWord_5802251) baseStart_5802251 baseEnd_5802251 := by
    simpa [prefixWord, tailWord_5802251, baseEnd_5802251] using wordTrace_append hprefix tailTrace_5802251
  have hstable : (prefixWord ++ tailWord_5802251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5802251).length < 2 ^ (prefixWord ++ tailWord_5802251).sum := by decide
  have hdescent : baseEnd_5802251 < baseStart_5802251 := by decide
  rcases family_descends (prefixWord ++ tailWord_5802251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5802286 : List Nat := [4, 1, 3, 3, 2, 1, 1, 1, 1, 3, 3]
def baseStart_5802286 : Nat := 118140960795 + 5802286 * 2 ^ 59
def prefixEnd_5802286 : Nat := 4983230072969 + 3 ^ 40 * 5802286 * 2
def baseEnd_5802286 : Nat := 2979361612853590763040779

theorem tailTrace_5802286 : CollatzResearch.WordTrace tailWord_5802286 prefixEnd_5802286 2979361612853590763040779 := by
  unfold tailWord_5802286
  simp only [CollatzResearch.WordTrace]
  refine ⟨26453344532164531050028339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141084504171544165600151141 26453344532164531050028339)
  ·
    refine ⟨39680016798246796575042509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26453344532164531050028339 39680016798246796575042509)
    ·
      refine ⟨14880006299342548715640941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39680016798246796575042509 14880006299342548715640941)
      ·
        refine ⟨5580002362253455768365353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14880006299342548715640941 5580002362253455768365353)
        ·
          refine ⟨4185001771690091826274015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5580002362253455768365353 4185001771690091826274015)
          ·
            refine ⟨6277502657535137739411023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4185001771690091826274015 6277502657535137739411023)
            ·
              refine ⟨9416253986302706609116535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6277502657535137739411023 9416253986302706609116535)
              ·
                refine ⟨14124380979454059913674803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9416253986302706609116535 14124380979454059913674803)
                ·
                  refine ⟨21186571469181089870512205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14124380979454059913674803 21186571469181089870512205)
                  ·
                    refine ⟨7944964300942908701442077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21186571469181089870512205 7944964300942908701442077)
                    ·
                      refine ⟨2979361612853590763040779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7944964300942908701442077 2979361612853590763040779)
                      ·
                        rfl

theorem cell23_5802286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_5802286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5802286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5802286 prefixEnd_5802286 := by exact prefixLift 5802286
  have htrace : WordTrace (prefixWord ++ tailWord_5802286) baseStart_5802286 baseEnd_5802286 := by
    simpa [prefixWord, tailWord_5802286, baseEnd_5802286] using wordTrace_append hprefix tailTrace_5802286
  have hstable : (prefixWord ++ tailWord_5802286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5802286).length < 2 ^ (prefixWord ++ tailWord_5802286).sum := by decide
  have hdescent : baseEnd_5802286 < baseStart_5802286 := by decide
  rcases family_descends (prefixWord ++ tailWord_5802286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5802298 : List Nat := [3, 1, 1, 1, 4, 2, 2, 2, 7]
def baseStart_5802298 : Nat := 118140960795 + 5802298 * 2 ^ 59
def prefixEnd_5802298 : Nat := 4983230072969 + 3 ^ 40 * 5802298 * 2
def baseEnd_5802298 : Nat := 331040863846827190676747

theorem tailTrace_5802298 : CollatzResearch.WordTrace tailWord_5802298 prefixEnd_5802298 331040863846827190676747 := by
  unfold tailWord_5802298
  simp only [CollatzResearch.WordTrace]
  refine ⟨52906798483318193612415887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141084795955515182966442365 52906798483318193612415887)
  ·
    refine ⟨79360197724977290418623831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52906798483318193612415887 79360197724977290418623831)
    ·
      refine ⟨119040296587465935627935747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79360197724977290418623831 119040296587465935627935747)
      ·
        refine ⟨178560444881198903441903621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119040296587465935627935747 178560444881198903441903621)
        ·
          refine ⟨33480083415224794395356929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 178560444881198903441903621 33480083415224794395356929)
          ·
            refine ⟨25110062561418595796517697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33480083415224794395356929 25110062561418595796517697)
            ·
              refine ⟨18832546921063946847388273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25110062561418595796517697 18832546921063946847388273)
              ·
                refine ⟨14124410190797960135541205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18832546921063946847388273 14124410190797960135541205)
                ·
                  refine ⟨331040863846827190676747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14124410190797960135541205 331040863846827190676747)
                  ·
                    rfl

theorem cell23_5802298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 7].length) (baseStart_5802298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5802298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5802298 prefixEnd_5802298 := by exact prefixLift 5802298
  have htrace : WordTrace (prefixWord ++ tailWord_5802298) baseStart_5802298 baseEnd_5802298 := by
    simpa [prefixWord, tailWord_5802298, baseEnd_5802298] using wordTrace_append hprefix tailTrace_5802298
  have hstable : (prefixWord ++ tailWord_5802298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5802298).length < 2 ^ (prefixWord ++ tailWord_5802298).sum := by decide
  have hdescent : baseEnd_5802298 < baseStart_5802298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5802298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5802365 : List Nat := [1, 4, 1, 1, 2, 3, 1, 3, 2, 1, 4]
def baseStart_5802365 : Nat := 118140960795 + 5802365 * 2 ^ 59
def prefixEnd_5802365 : Nat := 4983230072969 + 3 ^ 40 * 5802365 * 2
def baseEnd_5802365 : Nat := 2979402177825295953952915

theorem tailTrace_5802365 : CollatzResearch.WordTrace tailWord_5802365 prefixEnd_5802365 2979402177825295953952915 := by
  unfold tailWord_5802365
  simp only [CollatzResearch.WordTrace]
  refine ⟨211629637624030044892352549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141086425082686696594901699 211629637624030044892352549)
  ·
    refine ⟨39680557054505633417316103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 211629637624030044892352549 39680557054505633417316103)
    ·
      refine ⟨59520835581758450125974155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39680557054505633417316103 59520835581758450125974155)
      ·
        refine ⟨89281253372637675188961233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59520835581758450125974155 89281253372637675188961233)
        ·
          refine ⟨66960940029478256391720925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89281253372637675188961233 66960940029478256391720925)
          ·
            refine ⟨25110352511054346146895347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66960940029478256391720925 25110352511054346146895347)
            ·
              refine ⟨37665528766581519220343021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25110352511054346146895347 37665528766581519220343021)
              ·
                refine ⟨14124573287468069707628633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37665528766581519220343021 14124573287468069707628633)
                ·
                  refine ⟨10593429965601052280721475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14124573287468069707628633 10593429965601052280721475)
                  ·
                    refine ⟨15890144948401578421082213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10593429965601052280721475 15890144948401578421082213)
                    ·
                      refine ⟨2979402177825295953952915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15890144948401578421082213 2979402177825295953952915)
                      ·
                        rfl

theorem cell23_5802365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_5802365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5802365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5802365 prefixEnd_5802365 := by exact prefixLift 5802365
  have htrace : WordTrace (prefixWord ++ tailWord_5802365) baseStart_5802365 baseEnd_5802365 := by
    simpa [prefixWord, tailWord_5802365, baseEnd_5802365] using wordTrace_append hprefix tailTrace_5802365
  have hstable : (prefixWord ++ tailWord_5802365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5802365).length < 2 ^ (prefixWord ++ tailWord_5802365).sum := by decide
  have hdescent : baseEnd_5802365 < baseStart_5802365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5802365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5802382 : List Nat := [4, 1, 1, 4, 1, 1, 2, 2, 2, 1, 4]
def baseStart_5802382 : Nat := 118140960795 + 5802382 * 2 ^ 59
def prefixEnd_5802382 : Nat := 4983230072969 + 3 ^ 40 * 5802382 * 2
def baseEnd_5802382 : Nat := 2979410906996422387440337

theorem tailTrace_5802382 : CollatzResearch.WordTrace tailWord_5802382 prefixEnd_5802382 2979410906996422387440337 := by
  unfold tailWord_5802382
  simp only [CollatzResearch.WordTrace]
  refine ⟨26453782208121057099465175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141086838443312304530480933 26453782208121057099465175)
  ·
    refine ⟨39680673312181585649197763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26453782208121057099465175 39680673312181585649197763)
    ·
      refine ⟨59521009968272378473796645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39680673312181585649197763 59521009968272378473796645)
      ·
        refine ⟨11160189369051070963836871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59521009968272378473796645 11160189369051070963836871)
        ·
          refine ⟨16740284053576606445755307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11160189369051070963836871 16740284053576606445755307)
          ·
            refine ⟨25110426080364909668632961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16740284053576606445755307 25110426080364909668632961)
            ·
              refine ⟨18832819560273682251474721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25110426080364909668632961 18832819560273682251474721)
              ·
                refine ⟨14124614670205261688606041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18832819560273682251474721 14124614670205261688606041)
                ·
                  refine ⟨10593461002653946266454531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14124614670205261688606041 10593461002653946266454531)
                  ·
                    refine ⟨15890191503980919399681797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10593461002653946266454531 15890191503980919399681797)
                    ·
                      refine ⟨2979410906996422387440337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15890191503980919399681797 2979410906996422387440337)
                      ·
                        rfl

theorem cell23_5802382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_5802382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5802382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5802382 prefixEnd_5802382 := by exact prefixLift 5802382
  have htrace : WordTrace (prefixWord ++ tailWord_5802382) baseStart_5802382 baseEnd_5802382 := by
    simpa [prefixWord, tailWord_5802382, baseEnd_5802382] using wordTrace_append hprefix tailTrace_5802382
  have hstable : (prefixWord ++ tailWord_5802382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5802382).length < 2 ^ (prefixWord ++ tailWord_5802382).sum := by decide
  have hdescent : baseEnd_5802382 < baseStart_5802382 := by decide
  rcases family_descends (prefixWord ++ tailWord_5802382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5802442 : List Nat := [3, 1, 2, 1, 2, 2, 2, 1, 4, 3, 2]
def baseStart_5802442 : Nat := 118140960795 + 5802442 * 2 ^ 59
def prefixEnd_5802442 : Nat := 4983230072969 + 3 ^ 40 * 5802442 * 2
def baseEnd_5802442 : Nat := 2979441715835692152690061

theorem tailTrace_5802442 : CollatzResearch.WordTrace tailWord_5802442 prefixEnd_5802442 2979441715835692152690061 := by
  unfold tailWord_5802442
  simp only [CollatzResearch.WordTrace]
  refine ⟨52908111511187771760726395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141088297363167391361937053 52908111511187771760726395)
  ·
    refine ⟨79362167266781657641089593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52908111511187771760726395 79362167266781657641089593)
    ·
      refine ⟨59521625450086243230817195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79362167266781657641089593 59521625450086243230817195)
      ·
        refine ⟨89282438175129364846225793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59521625450086243230817195 89282438175129364846225793)
        ·
          refine ⟨66961828631347023634669345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89282438175129364846225793 66961828631347023634669345)
          ·
            refine ⟨50221371473510267726002009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66961828631347023634669345 50221371473510267726002009)
            ·
              refine ⟨37666028605132700794501507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50221371473510267726002009 37666028605132700794501507)
              ·
                refine ⟨56499042907699051191752261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37666028605132700794501507 56499042907699051191752261)
                ·
                  refine ⟨10593570545193572098453549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56499042907699051191752261 10593570545193572098453549)
                  ·
                    refine ⟨3972588954447589536920081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10593570545193572098453549 3972588954447589536920081)
                    ·
                      refine ⟨2979441715835692152690061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3972588954447589536920081 2979441715835692152690061)
                      ·
                        rfl

theorem cell23_5802442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 4, 3, 2].length) (baseStart_5802442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5802442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5802442 prefixEnd_5802442 := by exact prefixLift 5802442
  have htrace : WordTrace (prefixWord ++ tailWord_5802442) baseStart_5802442 baseEnd_5802442 := by
    simpa [prefixWord, tailWord_5802442, baseEnd_5802442] using wordTrace_append hprefix tailTrace_5802442
  have hstable : (prefixWord ++ tailWord_5802442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5802442).length < 2 ^ (prefixWord ++ tailWord_5802442).sum := by decide
  have hdescent : baseEnd_5802442 < baseStart_5802442 := by decide
  rcases family_descends (prefixWord ++ tailWord_5802442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5802469 : List Nat := [1, 3, 1, 5, 2, 1, 2, 2, 1, 5]
def baseStart_5802469 : Nat := 118140960795 + 5802469 * 2 ^ 59
def prefixEnd_5802469 : Nat := 4983230072969 + 3 ^ 40 * 5802469 * 2
def baseEnd_5802469 : Nat := 993151859937787849017479

theorem tailTrace_5802469 : CollatzResearch.WordTrace tailWord_5802469 prefixEnd_5802469 993151859937787849017479 := by
  unfold tailWord_5802469
  simp only [CollatzResearch.WordTrace]
  refine ⟨211633430815653270654138461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141088953877102180436092307 211633430815653270654138461)
  ·
    refine ⟨79362536555869976495301923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211633430815653270654138461 79362536555869976495301923)
    ·
      refine ⟨119043804833804964742952885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79362536555869976495301923 119043804833804964742952885)
      ·
        refine ⟨11160356703169215444651833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 119043804833804964742952885 11160356703169215444651833)
        ·
          refine ⟨8370267527376911583488875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11160356703169215444651833 8370267527376911583488875)
          ·
            refine ⟨12555401291065367375233313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8370267527376911583488875 12555401291065367375233313)
            ·
              refine ⟨9416550968299025531424985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12555401291065367375233313 9416550968299025531424985)
              ·
                refine ⟨7062413226224269148568739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9416550968299025531424985 7062413226224269148568739)
                ·
                  refine ⟨10593619839336403722853109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7062413226224269148568739 10593619839336403722853109)
                  ·
                    refine ⟨993151859937787849017479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10593619839336403722853109 993151859937787849017479)
                    ·
                      rfl

theorem cell23_5802469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 2, 1, 5].length) (baseStart_5802469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5802469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5802469 prefixEnd_5802469 := by exact prefixLift 5802469
  have htrace : WordTrace (prefixWord ++ tailWord_5802469) baseStart_5802469 baseEnd_5802469 := by
    simpa [prefixWord, tailWord_5802469, baseEnd_5802469] using wordTrace_append hprefix tailTrace_5802469
  have hstable : (prefixWord ++ tailWord_5802469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5802469).length < 2 ^ (prefixWord ++ tailWord_5802469).sum := by decide
  have hdescent : baseEnd_5802469 < baseStart_5802469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5802469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5802472 : List Nat := [2, 1, 4, 1, 1, 3, 1, 4, 1, 1, 4]
def baseStart_5802472 : Nat := 118140960795 + 5802472 * 2 ^ 59
def prefixEnd_5802472 : Nat := 4983230072969 + 3 ^ 40 * 5802472 * 2
def baseEnd_5802472 : Nat := 2979457120255327035314923

theorem tailTrace_5802472 : CollatzResearch.WordTrace tailWord_5802472 prefixEnd_5802472 2979457120255327035314923 := by
  unfold tailWord_5802472
  simp only [CollatzResearch.WordTrace]
  refine ⟨105816770117321201083248835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141089026823094934777665113 105816770117321201083248835)
  ·
    refine ⟨158725155175981801624873253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105816770117321201083248835 158725155175981801624873253)
    ·
      refine ⟨29760966595496587804663735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158725155175981801624873253 29760966595496587804663735)
      ·
        refine ⟨44641449893244881706995603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29760966595496587804663735 44641449893244881706995603)
        ·
          refine ⟨66962174839867322560493405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44641449893244881706995603 66962174839867322560493405)
          ·
            refine ⟨25110815564950245960185027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66962174839867322560493405 25110815564950245960185027)
            ·
              refine ⟨37666223347425368940277541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25110815564950245960185027 37666223347425368940277541)
              ·
                refine ⟨7062416877642256676302039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37666223347425368940277541 7062416877642256676302039)
                ·
                  refine ⟨10593625316463385014453059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7062416877642256676302039 10593625316463385014453059)
                  ·
                    refine ⟨15890437974695077521679589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10593625316463385014453059 15890437974695077521679589)
                    ·
                      refine ⟨2979457120255327035314923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15890437974695077521679589 2979457120255327035314923)
                      ·
                        rfl

theorem cell23_5802472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_5802472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5802472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5802472 prefixEnd_5802472 := by exact prefixLift 5802472
  have htrace : WordTrace (prefixWord ++ tailWord_5802472) baseStart_5802472 baseEnd_5802472 := by
    simpa [prefixWord, tailWord_5802472, baseEnd_5802472] using wordTrace_append hprefix tailTrace_5802472
  have hstable : (prefixWord ++ tailWord_5802472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5802472).length < 2 ^ (prefixWord ++ tailWord_5802472).sum := by decide
  have hdescent : baseEnd_5802472 < baseStart_5802472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5802472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5802505 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 5, 3, 3]
def baseStart_5802505 : Nat := 118140960795 + 5802505 * 2 ^ 59
def prefixEnd_5802505 : Nat := 4983230072969 + 3 ^ 40 * 5802505 * 2
def baseEnd_5802505 : Nat := 2979474065116925406202271

theorem tailTrace_5802505 : CollatzResearch.WordTrace tailWord_5802505 prefixEnd_5802505 2979474065116925406202271 := by
  unfold tailWord_5802505
  simp only [CollatzResearch.WordTrace]
  refine ⟨211634743843522848802448969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141089829229015232534965979 211634743843522848802448969)
  ·
    refine ⟨158726057882642136601836727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211634743843522848802448969 158726057882642136601836727)
    ·
      refine ⟨238089086823963204902755091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158726057882642136601836727 238089086823963204902755091)
      ·
        refine ⟨357133630235944807354132637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238089086823963204902755091 357133630235944807354132637)
        ·
          refine ⟨133925111338479302757799739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 357133630235944807354132637 133925111338479302757799739)
          ·
            refine ⟨200887667007718954136699609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133925111338479302757799739 200887667007718954136699609)
            ·
              refine ⟨150665750255789215602524707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200887667007718954136699609 150665750255789215602524707)
              ·
                refine ⟨225998625383683823403787061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150665750255789215602524707 225998625383683823403787061)
                ·
                  refine ⟨21187371129720358444105037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 225998625383683823403787061 21187371129720358444105037)
                  ·
                    refine ⟨7945264173645134416539389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21187371129720358444105037 7945264173645134416539389)
                    ·
                      refine ⟨2979474065116925406202271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7945264173645134416539389 2979474065116925406202271)
                      ·
                        rfl

theorem cell23_5802505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 3, 3].length) (baseStart_5802505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5802505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5802505 prefixEnd_5802505 := by exact prefixLift 5802505
  have htrace : WordTrace (prefixWord ++ tailWord_5802505) baseStart_5802505 baseEnd_5802505 := by
    simpa [prefixWord, tailWord_5802505, baseEnd_5802505] using wordTrace_append hprefix tailTrace_5802505
  have hstable : (prefixWord ++ tailWord_5802505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5802505).length < 2 ^ (prefixWord ++ tailWord_5802505).sum := by decide
  have hdescent : baseEnd_5802505 < baseStart_5802505 := by decide
  rcases family_descends (prefixWord ++ tailWord_5802505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5802516 : List Nat := [2, 4, 3, 1, 1, 2, 1, 3, 2, 4]
def baseStart_5802516 : Nat := 118140960795 + 5802516 * 2 ^ 59
def prefixEnd_5802516 : Nat := 4983230072969 + 3 ^ 40 * 5802516 * 2
def baseEnd_5802516 : Nat := 993159904468041621054907

theorem tailTrace_5802516 : CollatzResearch.WordTrace tailWord_5802516 prefixEnd_5802516 993159904468041621054907 := by
  unfold tailWord_5802516
  simp only [CollatzResearch.WordTrace]
  refine ⟨105817572523241498840549701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141090096697655331787399601 105817572523241498840549701)
  ·
    refine ⟨19840794848107781032603069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105817572523241498840549701 19840794848107781032603069)
    ·
      refine ⟨7440298068040417887226151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19840794848107781032603069 7440298068040417887226151)
      ·
        refine ⟨11160447102060626830839227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7440298068040417887226151 11160447102060626830839227)
        ·
          refine ⟨16740670653090940246258841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11160447102060626830839227 16740670653090940246258841)
          ·
            refine ⟨12555502989818205184694131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16740670653090940246258841 12555502989818205184694131)
            ·
              refine ⟨18833254484727307777041197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12555502989818205184694131 18833254484727307777041197)
              ·
                refine ⟨7062470431772740416390449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18833254484727307777041197 7062470431772740416390449)
                ·
                  refine ⟨5296852823829555312292837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7062470431772740416390449 5296852823829555312292837)
                  ·
                    refine ⟨993159904468041621054907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5296852823829555312292837 993159904468041621054907)
                    ·
                      rfl

theorem cell23_5802516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_5802516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5802516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5802516 prefixEnd_5802516 := by exact prefixLift 5802516
  have htrace : WordTrace (prefixWord ++ tailWord_5802516) baseStart_5802516 baseEnd_5802516 := by
    simpa [prefixWord, tailWord_5802516, baseEnd_5802516] using wordTrace_append hprefix tailTrace_5802516
  have hstable : (prefixWord ++ tailWord_5802516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5802516).length < 2 ^ (prefixWord ++ tailWord_5802516).sum := by decide
  have hdescent : baseEnd_5802516 < baseStart_5802516 := by decide
  rcases family_descends (prefixWord ++ tailWord_5802516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5802556 : List Nat := [2, 2, 2, 2, 3, 2, 2, 2, 2, 1, 3]
def baseStart_5802556 : Nat := 118140960795 + 5802556 * 2 ^ 59
def prefixEnd_5802556 : Nat := 4983230072969 + 3 ^ 40 * 5802556 * 2
def baseEnd_5802556 : Nat := 2979500252630304706664537

theorem tailTrace_5802556 : CollatzResearch.WordTrace tailWord_5802556 prefixEnd_5802556 2979500252630304706664537 := by
  unfold tailWord_5802556
  simp only [CollatzResearch.WordTrace]
  refine ⟨105818301983169042256277761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141091069310892056341703681 105818301983169042256277761)
  ·
    refine ⟨79363726487376781692208321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105818301983169042256277761 79363726487376781692208321)
    ·
      refine ⟨59522794865532586269156241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79363726487376781692208321 59522794865532586269156241)
      ·
        refine ⟨44642096149149439701867181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59522794865532586269156241 44642096149149439701867181)
        ·
          refine ⟨16740786055931039888200193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44642096149149439701867181 16740786055931039888200193)
          ·
            refine ⟨12555589541948279916150145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16740786055931039888200193 12555589541948279916150145)
            ·
              refine ⟨9416692156461209937112609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12555589541948279916150145 9416692156461209937112609)
              ·
                refine ⟨7062519117345907452834457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9416692156461209937112609 7062519117345907452834457)
                ·
                  refine ⟨5296889338009430589625843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7062519117345907452834457 5296889338009430589625843)
                  ·
                    refine ⟨7945334007014145884438765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5296889338009430589625843 7945334007014145884438765)
                    ·
                      refine ⟨2979500252630304706664537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7945334007014145884438765 2979500252630304706664537)
                      ·
                        rfl

theorem cell23_5802556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_5802556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5802556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5802556 prefixEnd_5802556 := by exact prefixLift 5802556
  have htrace : WordTrace (prefixWord ++ tailWord_5802556) baseStart_5802556 baseEnd_5802556 := by
    simpa [prefixWord, tailWord_5802556, baseEnd_5802556] using wordTrace_append hprefix tailTrace_5802556
  have hstable : (prefixWord ++ tailWord_5802556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5802556).length < 2 ^ (prefixWord ++ tailWord_5802556).sum := by decide
  have hdescent : baseEnd_5802556 < baseStart_5802556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5802556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5802575 : List Nat := [1, 1, 2, 1, 1, 2, 5, 1, 1, 4, 4]
def baseStart_5802575 : Nat := 118140960795 + 5802575 * 2 ^ 59
def prefixEnd_5802575 : Nat := 4983230072969 + 3 ^ 40 * 5802575 * 2
def baseEnd_5802575 : Nat := 2979510008762740132326949

theorem tailTrace_5802575 : CollatzResearch.WordTrace tailWord_5802575 prefixEnd_5802575 2979510008762740132326949 := by
  unfold tailWord_5802575
  simp only [CollatzResearch.WordTrace]
  refine ⟨211637296953269250757497179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141091531302179500504998119 211637296953269250757497179)
  ·
    refine ⟨317455945429903876136245769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211637296953269250757497179 317455945429903876136245769)
    ·
      refine ⟨238091959072427907102184327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317455945429903876136245769 238091959072427907102184327)
      ·
        refine ⟨357137938608641860653276491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238091959072427907102184327 357137938608641860653276491)
        ·
          refine ⟨535706907912962790979914737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357137938608641860653276491 535706907912962790979914737)
          ·
            refine ⟨401780180934722093234936053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 535706907912962790979914737 401780180934722093234936053)
            ·
              refine ⟨37666891962630196240775255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 401780180934722093234936053 37666891962630196240775255)
              ·
                refine ⟨56500337943945294361162883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37666891962630196240775255 56500337943945294361162883)
                ·
                  refine ⟨84750506915917941541744325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56500337943945294361162883 84750506915917941541744325)
                  ·
                    refine ⟨15890720046734614039077061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 84750506915917941541744325 15890720046734614039077061)
                    ·
                      refine ⟨2979510008762740132326949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15890720046734614039077061 2979510008762740132326949)
                      ·
                        rfl

theorem cell23_5802575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 4, 4].length) (baseStart_5802575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5802575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5802575 prefixEnd_5802575 := by exact prefixLift 5802575
  have htrace : WordTrace (prefixWord ++ tailWord_5802575) baseStart_5802575 baseEnd_5802575 := by
    simpa [prefixWord, tailWord_5802575, baseEnd_5802575] using wordTrace_append hprefix tailTrace_5802575
  have hstable : (prefixWord ++ tailWord_5802575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5802575).length < 2 ^ (prefixWord ++ tailWord_5802575).sum := by decide
  have hdescent : baseEnd_5802575 < baseStart_5802575 := by decide
  rcases family_descends (prefixWord ++ tailWord_5802575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5802600 : List Nat := [2, 1, 4, 3, 2, 2, 2, 1, 1, 3, 2]
def baseStart_5802600 : Nat := 118140960795 + 5802600 * 2 ^ 59
def prefixEnd_5802600 : Nat := 4983230072969 + 3 ^ 40 * 5802600 * 2
def baseEnd_5802600 : Nat := 2979522845779102534514335

theorem tailTrace_5802600 : CollatzResearch.WordTrace tailWord_5802600 prefixEnd_5802600 2979522845779102534514335 := by
  unfold tailWord_5802600
  simp only [CollatzResearch.WordTrace]
  refine ⟨105819104389089340013578627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141092139185452453351438169 105819104389089340013578627)
  ·
    refine ⟨158728656583634010020367941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105819104389089340013578627 158728656583634010020367941)
    ·
      refine ⟨29761623109431376878818989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158728656583634010020367941 29761623109431376878818989)
      ·
        refine ⟨11160608666036766329557121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29761623109431376878818989 11160608666036766329557121)
        ·
          refine ⟨8370456499527574747167841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11160608666036766329557121 8370456499527574747167841)
          ·
            refine ⟨6277842374645681060375881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8370456499527574747167841 6277842374645681060375881)
            ·
              refine ⟨4708381780984260795281911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6277842374645681060375881 4708381780984260795281911)
              ·
                refine ⟨7062572671476391192922867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4708381780984260795281911 7062572671476391192922867)
                ·
                  refine ⟨10593859007214586789384301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7062572671476391192922867 10593859007214586789384301)
                  ·
                    refine ⟨3972697127705470046019113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10593859007214586789384301 3972697127705470046019113)
                    ·
                      refine ⟨2979522845779102534514335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3972697127705470046019113 2979522845779102534514335)
                      ·
                        rfl

theorem cell23_5802600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_5802600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5802600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5802600 prefixEnd_5802600 := by exact prefixLift 5802600
  have htrace : WordTrace (prefixWord ++ tailWord_5802600) baseStart_5802600 baseEnd_5802600 := by
    simpa [prefixWord, tailWord_5802600, baseEnd_5802600] using wordTrace_append hprefix tailTrace_5802600
  have hstable : (prefixWord ++ tailWord_5802600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5802600).length < 2 ^ (prefixWord ++ tailWord_5802600).sum := by decide
  have hdescent : baseEnd_5802600 < baseStart_5802600 := by decide
  rcases family_descends (prefixWord ++ tailWord_5802600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5802613 : List Nat := [1, 3, 4, 2, 2, 1, 1, 1, 4, 2, 2]
def baseStart_5802613 : Nat := 118140960795 + 5802613 * 2 ^ 59
def prefixEnd_5802613 : Nat := 4983230072969 + 3 ^ 40 * 5802613 * 2
def baseEnd_5802613 : Nat := 2979529521027610983651775

theorem tailTrace_5802613 : CollatzResearch.WordTrace tailWord_5802613 prefixEnd_5802613 2979529521027610983651775 := by
  unfold tailWord_5802613
  simp only [CollatzResearch.WordTrace]
  refine ⟨211638682927131583247380493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141092455284754388831586995 211638682927131583247380493)
  ·
    refine ⟨79364506097674343717767685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211638682927131583247380493 79364506097674343717767685)
    ·
      refine ⟨14880844893313939447081441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79364506097674343717767685 14880844893313939447081441)
      ·
        refine ⟨11160633669985454585311081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14880844893313939447081441 11160633669985454585311081)
        ·
          refine ⟨8370475252489090938983311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11160633669985454585311081 8370475252489090938983311)
          ·
            refine ⟨12555712878733636408474967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8370475252489090938983311 12555712878733636408474967)
            ·
              refine ⟨18833569318100454612712451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12555712878733636408474967 18833569318100454612712451)
              ·
                refine ⟨28250353977150681919068677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18833569318100454612712451 28250353977150681919068677)
                ·
                  refine ⟨5296941370715752859825377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28250353977150681919068677 5296941370715752859825377)
                  ·
                    refine ⟨3972706028036814644869033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5296941370715752859825377 3972706028036814644869033)
                    ·
                      refine ⟨2979529521027610983651775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3972706028036814644869033 2979529521027610983651775)
                      ·
                        rfl

theorem cell23_5802613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_5802613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5802613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5802613 prefixEnd_5802613 := by exact prefixLift 5802613
  have htrace : WordTrace (prefixWord ++ tailWord_5802613) baseStart_5802613 baseEnd_5802613 := by
    simpa [prefixWord, tailWord_5802613, baseEnd_5802613] using wordTrace_append hprefix tailTrace_5802613
  have hstable : (prefixWord ++ tailWord_5802613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5802613).length < 2 ^ (prefixWord ++ tailWord_5802613).sum := by decide
  have hdescent : baseEnd_5802613 < baseStart_5802613 := by decide
  rcases family_descends (prefixWord ++ tailWord_5802613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5802669 : List Nat := [1, 5, 2, 1, 1, 2, 1, 1, 4, 1, 4]
def baseStart_5802669 : Nat := 118140960795 + 5802669 * 2 ^ 59
def prefixEnd_5802669 : Nat := 4983230072969 + 3 ^ 40 * 5802669 * 2
def baseEnd_5802669 : Nat := 2979558275944262764551517

theorem tailTrace_5802669 : CollatzResearch.WordTrace tailWord_5802669 prefixEnd_5802669 2979558275944262764551517 := by
  unfold tailWord_5802669
  simp only [CollatzResearch.WordTrace]
  refine ⟨211640725414928704811419061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141093816943285803207612707 211640725414928704811419061)
  ·
    refine ⟨19841318007649566076070537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 211640725414928704811419061 19841318007649566076070537)
    ·
      refine ⟨14880988505737174557052903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19841318007649566076070537 14880988505737174557052903)
      ·
        refine ⟨22321482758605761835579355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14880988505737174557052903 22321482758605761835579355)
        ·
          refine ⟨33482224137908642753369033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22321482758605761835579355 33482224137908642753369033)
          ·
            refine ⟨25111668103431482065026775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33482224137908642753369033 25111668103431482065026775)
            ·
              refine ⟨37667502155147223097540163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25111668103431482065026775 37667502155147223097540163)
              ·
                refine ⟨56501253232720834646310245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37667502155147223097540163 56501253232720834646310245)
                ·
                  refine ⟨10593984981135156496183171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56501253232720834646310245 10593984981135156496183171)
                  ·
                    refine ⟨15890977471702734744274757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10593984981135156496183171 15890977471702734744274757)
                    ·
                      refine ⟨2979558275944262764551517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15890977471702734744274757 2979558275944262764551517)
                      ·
                        rfl

theorem cell23_5802669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_5802669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5802669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5802669 prefixEnd_5802669 := by exact prefixLift 5802669
  have htrace : WordTrace (prefixWord ++ tailWord_5802669) baseStart_5802669 baseEnd_5802669 := by
    simpa [prefixWord, tailWord_5802669, baseEnd_5802669] using wordTrace_append hprefix tailTrace_5802669
  have hstable : (prefixWord ++ tailWord_5802669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5802669).length < 2 ^ (prefixWord ++ tailWord_5802669).sum := by decide
  have hdescent : baseEnd_5802669 < baseStart_5802669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5802669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5802776 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 7, 2, 2]
def baseStart_5802776 : Nat := 118140960795 + 5802776 * 2 ^ 59
def prefixEnd_5802776 : Nat := 4983230072969 + 3 ^ 40 * 5802776 * 2
def baseEnd_5802776 : Nat := 2979613218374293845913525

theorem tailTrace_5802776 : CollatzResearch.WordTrace tailWord_5802776 prefixEnd_5802776 2979613218374293845913525 := by
  unfold tailWord_5802776
  simp only [CollatzResearch.WordTrace]
  refine ⟨105822314012770531042782091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141096418683694041390376121 105822314012770531042782091)
  ·
    refine ⟨158733471019155796564173137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105822314012770531042782091 158733471019155796564173137)
    ·
      refine ⟨119050103264366847423129853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158733471019155796564173137 119050103264366847423129853)
      ·
        refine ⟨44643788724137567783673695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119050103264366847423129853 44643788724137567783673695)
        ·
          refine ⟨66965683086206351675510543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44643788724137567783673695 66965683086206351675510543)
          ·
            refine ⟨100448524629309527513265815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66965683086206351675510543 100448524629309527513265815)
            ·
              refine ⟨150672786943964291269898723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100448524629309527513265815 150672786943964291269898723)
              ·
                refine ⟨226009180415946436904848085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150672786943964291269898723 226009180415946436904848085)
                ·
                  refine ⟨5297090165998744614957377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 226009180415946436904848085 5297090165998744614957377)
                  ·
                    refine ⟨3972817624499058461218033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5297090165998744614957377 3972817624499058461218033)
                    ·
                      refine ⟨2979613218374293845913525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3972817624499058461218033 2979613218374293845913525)
                      ·
                        rfl

theorem cell23_5802776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 7, 2, 2].length) (baseStart_5802776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5802776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5802776 prefixEnd_5802776 := by exact prefixLift 5802776
  have htrace : WordTrace (prefixWord ++ tailWord_5802776) baseStart_5802776 baseEnd_5802776 := by
    simpa [prefixWord, tailWord_5802776, baseEnd_5802776] using wordTrace_append hprefix tailTrace_5802776
  have hstable : (prefixWord ++ tailWord_5802776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5802776).length < 2 ^ (prefixWord ++ tailWord_5802776).sum := by decide
  have hdescent : baseEnd_5802776 < baseStart_5802776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5802776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5802786 : List Nat := [3, 3, 1, 1, 2, 3, 1, 1, 4, 4]
def baseStart_5802786 : Nat := 118140960795 + 5802786 * 2 ^ 59
def prefixEnd_5802786 : Nat := 4983230072969 + 3 ^ 40 * 5802786 * 2
def baseEnd_5802786 : Nat := 993206117726946268929493

theorem tailTrace_5802786 : CollatzResearch.WordTrace tailWord_5802786 prefixEnd_5802786 993206117726946268929493 := by
  unfold tailWord_5802786
  simp only [CollatzResearch.WordTrace]
  refine ⟨52911248188876208448357053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141096661837003222528952141 52911248188876208448357053)
  ·
    refine ⟨19841718070828578168133895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52911248188876208448357053 19841718070828578168133895)
    ·
      refine ⟨29762577106242867252200843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19841718070828578168133895 29762577106242867252200843)
      ·
        refine ⟨44643865659364300878301265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29762577106242867252200843 44643865659364300878301265)
        ·
          refine ⟨33482899244523225658725949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44643865659364300878301265 33482899244523225658725949)
          ·
            refine ⟨12556087216696209622022231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33482899244523225658725949 12556087216696209622022231)
            ·
              refine ⟨18834130825044314433033347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12556087216696209622022231 18834130825044314433033347)
              ·
                refine ⟨28251196237566471649550021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18834130825044314433033347 28251196237566471649550021)
                ·
                  refine ⟨5297099294543713434290629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28251196237566471649550021 5297099294543713434290629)
                  ·
                    refine ⟨993206117726946268929493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5297099294543713434290629 993206117726946268929493)
                    ·
                      rfl

theorem cell23_5802786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_5802786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5802786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5802786 prefixEnd_5802786 := by exact prefixLift 5802786
  have htrace : WordTrace (prefixWord ++ tailWord_5802786) baseStart_5802786 baseEnd_5802786 := by
    simpa [prefixWord, tailWord_5802786, baseEnd_5802786] using wordTrace_append hprefix tailTrace_5802786
  have hstable : (prefixWord ++ tailWord_5802786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5802786).length < 2 ^ (prefixWord ++ tailWord_5802786).sum := by decide
  have hdescent : baseEnd_5802786 < baseStart_5802786 := by decide
  rcases family_descends (prefixWord ++ tailWord_5802786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5802803 : List Nat := [1, 1, 1, 2, 6, 2, 3, 1, 2, 4]
def baseStart_5802803 : Nat := 118140960795 + 5802803 * 2 ^ 59
def prefixEnd_5802803 : Nat := 4983230072969 + 3 ^ 40 * 5802803 * 2
def baseEnd_5802803 : Nat := 993209027450655080091967

theorem tailTrace_5802803 : CollatzResearch.WordTrace tailWord_5802803 prefixEnd_5802803 993209027450655080091967 := by
  unfold tailWord_5802803
  simp only [CollatzResearch.WordTrace]
  refine ⟨211645612796443245696797063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141097075197628830464531375 211645612796443245696797063)
  ·
    refine ⟨317468419194664868545195595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211645612796443245696797063 317468419194664868545195595)
    ·
      refine ⟨476202628791997302817793393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317468419194664868545195595 476202628791997302817793393)
      ·
        refine ⟨357151971593997977113345045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 476202628791997302817793393 357151971593997977113345045)
        ·
          refine ⟨16741498668468655177188049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 357151971593997977113345045 16741498668468655177188049)
          ·
            refine ⟨12556124001351491382891037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16741498668468655177188049 12556124001351491382891037)
            ·
              refine ⟨4708546500506809268584139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12556124001351491382891037 4708546500506809268584139)
              ·
                refine ⟨7062819750760213902876209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4708546500506809268584139 7062819750760213902876209)
                ·
                  refine ⟨5297114813070160427157157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7062819750760213902876209 5297114813070160427157157)
                  ·
                    refine ⟨993209027450655080091967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5297114813070160427157157 993209027450655080091967)
                    ·
                      rfl

theorem cell23_5802803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 1, 2, 4].length) (baseStart_5802803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5802803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5802803 prefixEnd_5802803 := by exact prefixLift 5802803
  have htrace : WordTrace (prefixWord ++ tailWord_5802803) baseStart_5802803 baseEnd_5802803 := by
    simpa [prefixWord, tailWord_5802803, baseEnd_5802803] using wordTrace_append hprefix tailTrace_5802803
  have hstable : (prefixWord ++ tailWord_5802803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5802803).length < 2 ^ (prefixWord ++ tailWord_5802803).sum := by decide
  have hdescent : baseEnd_5802803 < baseStart_5802803 := by decide
  rcases family_descends (prefixWord ++ tailWord_5802803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5802844 : List Nat := [2, 2, 4, 2, 1, 2, 3, 2, 1, 2, 2]
def baseStart_5802844 : Nat := 118140960795 + 5802844 * 2 ^ 59
def prefixEnd_5802844 : Nat := 4983230072969 + 3 ^ 40 * 5802844 * 2
def baseEnd_5802844 : Nat := 2979648135058799579863213

theorem tailTrace_5802844 : CollatzResearch.WordTrace tailWord_5802844 prefixEnd_5802844 2979648135058799579863213 := by
  unfold tailWord_5802844
  simp only [CollatzResearch.WordTrace]
  refine ⟨105823554094647354849519793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141098072126196473132693057 105823554094647354849519793)
  ·
    refine ⟨79367665570985516137139845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105823554094647354849519793 79367665570985516137139845)
    ·
      refine ⟨14881437294559784275713721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79367665570985516137139845 14881437294559784275713721)
      ·
        refine ⟨11161077970919838206785291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14881437294559784275713721 11161077970919838206785291)
        ·
          refine ⟨16741616956379757310177937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11161077970919838206785291 16741616956379757310177937)
          ·
            refine ⟨12556212717284817982633453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16741616956379757310177937 12556212717284817982633453)
            ·
              refine ⟨4708579768981806743487545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12556212717284817982633453 4708579768981806743487545)
              ·
                refine ⟨3531434826736355057615659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4708579768981806743487545 3531434826736355057615659)
                ·
                  refine ⟨5297152240104532586423489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3531434826736355057615659 5297152240104532586423489)
                  ·
                    refine ⟨3972864180078399439817617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5297152240104532586423489 3972864180078399439817617)
                    ·
                      refine ⟨2979648135058799579863213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3972864180078399439817617 2979648135058799579863213)
                      ·
                        rfl

theorem cell23_5802844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_5802844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5802844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5802844 prefixEnd_5802844 := by exact prefixLift 5802844
  have htrace : WordTrace (prefixWord ++ tailWord_5802844) baseStart_5802844 baseEnd_5802844 := by
    simpa [prefixWord, tailWord_5802844, baseEnd_5802844] using wordTrace_append hprefix tailTrace_5802844
  have hstable : (prefixWord ++ tailWord_5802844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5802844).length < 2 ^ (prefixWord ++ tailWord_5802844).sum := by decide
  have hdescent : baseEnd_5802844 < baseStart_5802844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5802844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5802870 : List Nat := [5, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2]
def baseStart_5802870 : Nat := 118140960795 + 5802870 * 2 ^ 59
def prefixEnd_5802870 : Nat := 4983230072969 + 3 ^ 40 * 5802870 * 2
def baseEnd_5802870 : Nat := 2979661485555816478138093

theorem tailTrace_5802870 : CollatzResearch.WordTrace tailWord_5802870 prefixEnd_5802870 2979661485555816478138093 := by
  unfold tailWord_5802870
  simp only [CollatzResearch.WordTrace]
  refine ⟨13228003530450032258717879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141098704324800344092990709 13228003530450032258717879)
  ·
    refine ⟨19842005295675048388076819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13228003530450032258717879 19842005295675048388076819)
    ·
      refine ⟨29763007943512572582115229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19842005295675048388076819 29763007943512572582115229)
      ·
        refine ⟨11161127978817214718293211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29763007943512572582115229 11161127978817214718293211)
        ·
          refine ⟨16741691968225822077439817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11161127978817214718293211 16741691968225822077439817)
          ·
            refine ⟨12556268976169366558079863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16741691968225822077439817 12556268976169366558079863)
            ·
              refine ⟨18834403464254049837119795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12556268976169366558079863 18834403464254049837119795)
              ·
                refine ⟨28251605196381074755679693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18834403464254049837119795 28251605196381074755679693)
                ·
                  refine ⟨10594351948642903033379885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28251605196381074755679693 10594351948642903033379885)
                  ·
                    refine ⟨3972881980741088637517457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10594351948642903033379885 3972881980741088637517457)
                    ·
                      refine ⟨2979661485555816478138093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3972881980741088637517457 2979661485555816478138093)
                      ·
                        rfl

theorem cell23_5802870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_5802870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5802870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5802870 prefixEnd_5802870 := by exact prefixLift 5802870
  have htrace : WordTrace (prefixWord ++ tailWord_5802870) baseStart_5802870 baseEnd_5802870 := by
    simpa [prefixWord, tailWord_5802870, baseEnd_5802870] using wordTrace_append hprefix tailTrace_5802870
  have hstable : (prefixWord ++ tailWord_5802870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5802870).length < 2 ^ (prefixWord ++ tailWord_5802870).sum := by decide
  have hdescent : baseEnd_5802870 < baseStart_5802870 := by decide
  rcases family_descends (prefixWord ++ tailWord_5802870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5802916 : List Nat := [2, 3, 1, 2, 1, 2, 3, 1, 2, 3, 3]
def baseStart_5802916 : Nat := 118140960795 + 5802916 * 2 ^ 59
def prefixEnd_5802916 : Nat := 4983230072969 + 3 ^ 40 * 5802916 * 2
def baseEnd_5802916 : Nat := 2979685105665923298162881

theorem tailTrace_5802916 : CollatzResearch.WordTrace tailWord_5802916 prefixEnd_5802916 2979685105665923298162881 := by
  unfold tailWord_5802916
  simp only [CollatzResearch.WordTrace]
  refine ⟨105824867122516932997830301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141099822830022577330440401 105824867122516932997830301)
  ·
    refine ⟨39684325170943849874186363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105824867122516932997830301 39684325170943849874186363)
    ·
      refine ⟨59526487756415774811279545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39684325170943849874186363 59526487756415774811279545)
      ·
        refine ⟨44644865817311831108459659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59526487756415774811279545 44644865817311831108459659)
        ·
          refine ⟨66967298725967746662689489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44644865817311831108459659 66967298725967746662689489)
          ·
            refine ⟨50225474044475809997017117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66967298725967746662689489 50225474044475809997017117)
            ·
              refine ⟨18834552766678428748881419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50225474044475809997017117 18834552766678428748881419)
              ·
                refine ⟨28251829150017643123322129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18834552766678428748881419 28251829150017643123322129)
                ·
                  refine ⟨21188871862513232342491597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28251829150017643123322129 21188871862513232342491597)
                  ·
                    refine ⟨7945826948442462128434349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21188871862513232342491597 7945826948442462128434349)
                    ·
                      refine ⟨2979685105665923298162881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7945826948442462128434349 2979685105665923298162881)
                      ·
                        rfl

theorem cell23_5802916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_5802916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5802916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5802916 prefixEnd_5802916 := by exact prefixLift 5802916
  have htrace : WordTrace (prefixWord ++ tailWord_5802916) baseStart_5802916 baseEnd_5802916 := by
    simpa [prefixWord, tailWord_5802916, baseEnd_5802916] using wordTrace_append hprefix tailTrace_5802916
  have hstable : (prefixWord ++ tailWord_5802916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5802916).length < 2 ^ (prefixWord ++ tailWord_5802916).sum := by decide
  have hdescent : baseEnd_5802916 < baseStart_5802916 := by decide
  rcases family_descends (prefixWord ++ tailWord_5802916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5802936 : List Nat := [2, 1, 2, 1, 2, 4, 3, 1, 2, 5]
def baseStart_5802936 : Nat := 118140960795 + 5802936 * 2 ^ 59
def prefixEnd_5802936 : Nat := 4983230072969 + 3 ^ 40 * 5802936 * 2
def baseEnd_5802936 : Nat := 993231791759671073304263

theorem tailTrace_5802936 : CollatzResearch.WordTrace tailWord_5802936 prefixEnd_5802936 993231791759671073304263 := by
  unfold tailWord_5802936
  simp only [CollatzResearch.WordTrace]
  refine ⟨105825231852480704705694331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141100309136640939607592441 105825231852480704705694331)
  ·
    refine ⟨158737847778721057058541497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105825231852480704705694331 158737847778721057058541497)
    ·
      refine ⟨119053385834040792793906123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158737847778721057058541497 119053385834040792793906123)
      ·
        refine ⟨178580078751061189190859185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119053385834040792793906123 178580078751061189190859185)
        ·
          refine ⟨133935059063295891893144389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178580078751061189190859185 133935059063295891893144389)
          ·
            refine ⟨25112823574367979729964573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 133935059063295891893144389 25112823574367979729964573)
            ·
              refine ⟨9417308840387992398736715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25112823574367979729964573 9417308840387992398736715)
              ·
                refine ⟨14125963260581988598105073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9417308840387992398736715 14125963260581988598105073)
                ·
                  refine ⟨10594472445436491448578805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14125963260581988598105073 10594472445436491448578805)
                  ·
                    refine ⟨993231791759671073304263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10594472445436491448578805 993231791759671073304263)
                    ·
                      rfl

theorem cell23_5802936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 2, 5].length) (baseStart_5802936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5802936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5802936 prefixEnd_5802936 := by exact prefixLift 5802936
  have htrace : WordTrace (prefixWord ++ tailWord_5802936) baseStart_5802936 baseEnd_5802936 := by
    simpa [prefixWord, tailWord_5802936, baseEnd_5802936] using wordTrace_append hprefix tailTrace_5802936
  have hstable : (prefixWord ++ tailWord_5802936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5802936).length < 2 ^ (prefixWord ++ tailWord_5802936).sum := by decide
  have hdescent : baseEnd_5802936 < baseStart_5802936 := by decide
  rcases family_descends (prefixWord ++ tailWord_5802936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5802956 : List Nat := [2, 2, 1, 4, 1, 1, 2, 1, 4, 1, 4]
def baseStart_5802956 : Nat := 118140960795 + 5802956 * 2 ^ 59
def prefixEnd_5802956 : Nat := 4983230072969 + 3 ^ 40 * 5802956 * 2
def baseEnd_5802956 : Nat := 2979705644892103141662697

theorem tailTrace_5802956 : CollatzResearch.WordTrace tailWord_5802956 prefixEnd_5802956 2979705644892103141662697 := by
  unfold tailWord_5802956
  simp only [CollatzResearch.WordTrace]
  refine ⟨105825596582444476413558361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141100795443259301884744481 105825596582444476413558361)
  ·
    refine ⟨79369197436833357310168771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105825596582444476413558361 79369197436833357310168771)
    ·
      refine ⟨119053796155250035965253157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79369197436833357310168771 119053796155250035965253157)
      ·
        refine ⟨22322586779109381743484967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119053796155250035965253157 22322586779109381743484967)
        ·
          refine ⟨33483880168664072615227451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22322586779109381743484967 33483880168664072615227451)
          ·
            refine ⟨50225820252996108922841177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33483880168664072615227451 50225820252996108922841177)
            ·
              refine ⟨37669365189747081692130883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50225820252996108922841177 37669365189747081692130883)
              ·
                refine ⟨56504047784620622538196325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37669365189747081692130883 56504047784620622538196325)
                ·
                  refine ⟨10594508959616366725911811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56504047784620622538196325 10594508959616366725911811)
                  ·
                    refine ⟨15891763439424550088867717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10594508959616366725911811 15891763439424550088867717)
                    ·
                      refine ⟨2979705644892103141662697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15891763439424550088867717 2979705644892103141662697)
                      ·
                        rfl

theorem cell23_5802956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_5802956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5802956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5802956 prefixEnd_5802956 := by exact prefixLift 5802956
  have htrace : WordTrace (prefixWord ++ tailWord_5802956) baseStart_5802956 baseEnd_5802956 := by
    simpa [prefixWord, tailWord_5802956, baseEnd_5802956] using wordTrace_append hprefix tailTrace_5802956
  have hstable : (prefixWord ++ tailWord_5802956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5802956).length < 2 ^ (prefixWord ++ tailWord_5802956).sum := by decide
  have hdescent : baseEnd_5802956 < baseStart_5802956 := by decide
  rcases family_descends (prefixWord ++ tailWord_5802956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5802957 : List Nat := [1, 6, 3, 1, 1, 1, 2, 1, 7]
def baseStart_5802957 : Nat := 118140960795 + 5802957 * 2 ^ 59
def prefixEnd_5802957 : Nat := 4983230072969 + 3 ^ 40 * 5802957 * 2
def baseEnd_5802957 : Nat := 331078462041417515305577

theorem tailTrace_5802957 : CollatzResearch.WordTrace tailWord_5802957 prefixEnd_5802957 331078462041417515305577 := by
  unfold tailWord_5802957
  simp only [CollatzResearch.WordTrace]
  refine ⟨211651229637885329997903125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141100819758590219998602083 211651229637885329997903125)
  ·
    refine ⟨9921151389275874843651709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 211651229637885329997903125 9921151389275874843651709)
    ·
      refine ⟨3720431770978453066369391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9921151389275874843651709 3720431770978453066369391)
      ·
        refine ⟨5580647656467679599554087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3720431770978453066369391 5580647656467679599554087)
        ·
          refine ⟨8370971484701519399331131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5580647656467679599554087 8370971484701519399331131)
          ·
            refine ⟨12556457227052279098996697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8370971484701519399331131 12556457227052279098996697)
            ·
              refine ⟨9417342920289209324247523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12556457227052279098996697 9417342920289209324247523)
              ·
                refine ⟨14126014380433813986371285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9417342920289209324247523 14126014380433813986371285)
                ·
                  refine ⟨331078462041417515305577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14126014380433813986371285 331078462041417515305577)
                  ·
                    rfl

theorem cell23_5802957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_5802957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5802957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5802957 prefixEnd_5802957 := by exact prefixLift 5802957
  have htrace : WordTrace (prefixWord ++ tailWord_5802957) baseStart_5802957 baseEnd_5802957 := by
    simpa [prefixWord, tailWord_5802957, baseEnd_5802957] using wordTrace_append hprefix tailTrace_5802957
  have hstable : (prefixWord ++ tailWord_5802957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5802957).length < 2 ^ (prefixWord ++ tailWord_5802957).sum := by decide
  have hdescent : baseEnd_5802957 < baseStart_5802957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5802957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5802983 : List Nat := [1, 1, 5, 2, 2, 1, 2, 2, 3, 4]
def baseStart_5802983 : Nat := 118140960795 + 5802983 * 2 ^ 59
def prefixEnd_5802983 : Nat := 4983230072969 + 3 ^ 40 * 5802983 * 2
def baseEnd_5802983 : Nat := 993239836289924845341691

theorem tailTrace_5802983 : CollatzResearch.WordTrace tailWord_5802983 prefixEnd_5802983 993239836289924845341691 := by
  unfold tailWord_5802983
  simp only [CollatzResearch.WordTrace]
  refine ⟨211652177935791136438349603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141101451957194090958899735 211652177935791136438349603)
  ·
    refine ⟨317478266903686704657524405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211652177935791136438349603 317478266903686704657524405)
    ·
      refine ⟨29763587522220628561642913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 317478266903686704657524405 29763587522220628561642913)
      ·
        refine ⟨22322690641665471421232185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29763587522220628561642913 22322690641665471421232185)
        ·
          refine ⟨16742017981249103565924139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22322690641665471421232185 16742017981249103565924139)
          ·
            refine ⟨25113026971873655348886209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16742017981249103565924139 25113026971873655348886209)
            ·
              refine ⟨18834770228905241511664657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25113026971873655348886209 18834770228905241511664657)
              ·
                refine ⟨14126077671678931133748493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18834770228905241511664657 14126077671678931133748493)
                ·
                  refine ⟨5297279126879599175155685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14126077671678931133748493 5297279126879599175155685)
                  ·
                    refine ⟨993239836289924845341691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5297279126879599175155685 993239836289924845341691)
                    ·
                      rfl

theorem cell23_5802983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_5802983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5802983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5802983 prefixEnd_5802983 := by exact prefixLift 5802983
  have htrace : WordTrace (prefixWord ++ tailWord_5802983) baseStart_5802983 baseEnd_5802983 := by
    simpa [prefixWord, tailWord_5802983, baseEnd_5802983] using wordTrace_append hprefix tailTrace_5802983
  have hstable : (prefixWord ++ tailWord_5802983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5802983).length < 2 ^ (prefixWord ++ tailWord_5802983).sum := by decide
  have hdescent : baseEnd_5802983 < baseStart_5802983 := by decide
  rcases family_descends (prefixWord ++ tailWord_5802983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5803043 : List Nat := [1, 1, 1, 4, 3, 2, 3, 2, 1, 5]
def baseStart_5803043 : Nat := 118140960795 + 5803043 * 2 ^ 59
def prefixEnd_5803043 : Nat := 4983230072969 + 3 ^ 40 * 5803043 * 2
def baseEnd_5803043 : Nat := 993250105903014767091599

theorem tailTrace_5803043 : CollatzResearch.WordTrace tailWord_5803043 prefixEnd_5803043 993250105903014767091599 := by
  unfold tailWord_5803043
  simp only [CollatzResearch.WordTrace]
  refine ⟨211654366315573766685533783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141102910877049177790355855 211654366315573766685533783)
  ·
    refine ⟨317481549473360650028300675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211654366315573766685533783 317481549473360650028300675)
    ·
      refine ⟨476222324210040975042451013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317481549473360650028300675 476222324210040975042451013)
      ·
        refine ⟨89291685789382682820459565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 476222324210040975042451013 89291685789382682820459565)
        ·
          refine ⟨33484382171018506057672337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89291685789382682820459565 33484382171018506057672337)
          ·
            refine ⟨25113286628263879543254253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33484382171018506057672337 25113286628263879543254253)
            ·
              refine ⟨9417482485598954828720345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25113286628263879543254253 9417482485598954828720345)
              ·
                refine ⟨7063111864199216121540259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9417482485598954828720345 7063111864199216121540259)
                ·
                  refine ⟨10594667796298824182310389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7063111864199216121540259 10594667796298824182310389)
                  ·
                    refine ⟨993250105903014767091599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10594667796298824182310389 993250105903014767091599)
                    ·
                      rfl

theorem cell23_5803043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 2, 1, 5].length) (baseStart_5803043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5803043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5803043 prefixEnd_5803043 := by exact prefixLift 5803043
  have htrace : WordTrace (prefixWord ++ tailWord_5803043) baseStart_5803043 baseEnd_5803043 := by
    simpa [prefixWord, tailWord_5803043, baseEnd_5803043] using wordTrace_append hprefix tailTrace_5803043
  have hstable : (prefixWord ++ tailWord_5803043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5803043).length < 2 ^ (prefixWord ++ tailWord_5803043).sum := by decide
  have hdescent : baseEnd_5803043 < baseStart_5803043 := by decide
  rcases family_descends (prefixWord ++ tailWord_5803043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5803049 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 11]
def baseStart_5803049 : Nat := 118140960795 + 5803049 * 2 ^ 59
def prefixEnd_5803049 : Nat := 4983230072969 + 3 ^ 40 * 5803049 * 2
def baseEnd_5803049 : Nat := 2979753398592971277799769

theorem tailTrace_5803049 : CollatzResearch.WordTrace tailWord_5803049 prefixEnd_5803049 2979753398592971277799769 := by
  unfold tailWord_5803049
  simp only [CollatzResearch.WordTrace]
  refine ⟨211654585153552029710252201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141103056769034686473501467 211654585153552029710252201)
  ·
    refine ⟨158740938865164022282689151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211654585153552029710252201 158740938865164022282689151)
    ·
      refine ⟨238111408297746033424033727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158740938865164022282689151 238111408297746033424033727)
      ·
        refine ⟨357167112446619050136050591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238111408297746033424033727 357167112446619050136050591)
        ·
          refine ⟨535750668669928575204075887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357167112446619050136050591 535750668669928575204075887)
          ·
            refine ⟨803626003004892862806113831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 535750668669928575204075887 803626003004892862806113831)
            ·
              refine ⟨1205439004507339294209170747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 803626003004892862806113831 1205439004507339294209170747)
              ·
                refine ⟨1808158506761008941313756121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1205439004507339294209170747 1808158506761008941313756121)
                ·
                  refine ⟨1356118880070756705985317091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1808158506761008941313756121 1356118880070756705985317091)
                  ·
                    refine ⟨2034178320106135058977975637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1356118880070756705985317091 2034178320106135058977975637)
                    ·
                      refine ⟨2979753398592971277799769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 2034178320106135058977975637 2979753398592971277799769)
                      ·
                        rfl

theorem cell23_5803049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 11].length) (baseStart_5803049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5803049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5803049 prefixEnd_5803049 := by exact prefixLift 5803049
  have htrace : WordTrace (prefixWord ++ tailWord_5803049) baseStart_5803049 baseEnd_5803049 := by
    simpa [prefixWord, tailWord_5803049, baseEnd_5803049] using wordTrace_append hprefix tailTrace_5803049
  have hstable : (prefixWord ++ tailWord_5803049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5803049).length < 2 ^ (prefixWord ++ tailWord_5803049).sum := by decide
  have hdescent : baseEnd_5803049 < baseStart_5803049 := by decide
  rcases family_descends (prefixWord ++ tailWord_5803049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5803056 : List Nat := [2, 1, 1, 1, 2, 4, 3, 2, 1, 6]
def baseStart_5803056 : Nat := 118140960795 + 5803056 * 2 ^ 59
def prefixEnd_5803056 : Nat := 4983230072969 + 3 ^ 40 * 5803056 * 2
def baseEnd_5803056 : Nat := 993252330985850916804079

theorem tailTrace_5803056 : CollatzResearch.WordTrace tailWord_5803056 prefixEnd_5803056 993252330985850916804079 := by
  unfold tailWord_5803056
  simp only [CollatzResearch.WordTrace]
  refine ⟨105827420232263334952878511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141103226976351113270504681 105827420232263334952878511)
  ·
    refine ⟨158741130348395002429317767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105827420232263334952878511 158741130348395002429317767)
    ·
      refine ⟨238111695522592503643976651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158741130348395002429317767 238111695522592503643976651)
      ·
        refine ⟨357167543283888755465964977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238111695522592503643976651 357167543283888755465964977)
        ·
          refine ⟨267875657462916566599473733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 357167543283888755465964977 267875657462916566599473733)
          ·
            refine ⟨50226685774296856237401325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 267875657462916566599473733 50226685774296856237401325)
            ·
              refine ⟨18835007165361321089025497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50226685774296856237401325 18835007165361321089025497)
              ·
                refine ⟨14126255374020990816769123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18835007165361321089025497 14126255374020990816769123)
                ·
                  refine ⟨21189383061031486225153685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14126255374020990816769123 21189383061031486225153685)
                  ·
                    refine ⟨993252330985850916804079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21189383061031486225153685 993252330985850916804079)
                    ·
                      rfl

theorem cell23_5803056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 1, 6].length) (baseStart_5803056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5803056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5803056 prefixEnd_5803056 := by exact prefixLift 5803056
  have htrace : WordTrace (prefixWord ++ tailWord_5803056) baseStart_5803056 baseEnd_5803056 := by
    simpa [prefixWord, tailWord_5803056, baseEnd_5803056] using wordTrace_append hprefix tailTrace_5803056
  have hstable : (prefixWord ++ tailWord_5803056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5803056).length < 2 ^ (prefixWord ++ tailWord_5803056).sum := by decide
  have hdescent : baseEnd_5803056 < baseStart_5803056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5803056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5803080 : List Nat := [2, 1, 3, 1, 1, 1, 4, 3, 3, 2, 2]
def baseStart_5803080 : Nat := 118140960795 + 5803080 * 2 ^ 59
def prefixEnd_5803080 : Nat := 4983230072969 + 3 ^ 40 * 5803080 * 2
def baseEnd_5803080 : Nat := 2979769316493260656512127

theorem tailTrace_5803080 : CollatzResearch.WordTrace tailWord_5803080 prefixEnd_5803080 2979769316493260656512127 := by
  unfold tailWord_5803080
  simp only [CollatzResearch.WordTrace]
  refine ⟨105827857908219861002315347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141103810544293148003087129 105827857908219861002315347)
  ·
    refine ⟨158741786862329791503473021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105827857908219861002315347 158741786862329791503473021)
    ·
      refine ⟨59528170073373671813802383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158741786862329791503473021 59528170073373671813802383)
      ·
        refine ⟨89292255110060507720703575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59528170073373671813802383 89292255110060507720703575)
        ·
          refine ⟨133938382665090761581055363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89292255110060507720703575 133938382665090761581055363)
          ·
            refine ⟨200907573997636142371583045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133938382665090761581055363 200907573997636142371583045)
            ·
              refine ⟨37670170124556776694671821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 200907573997636142371583045 37670170124556776694671821)
              ·
                refine ⟨14126313796708791260501933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37670170124556776694671821 14126313796708791260501933)
                ·
                  refine ⟨5297367673765796722688225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14126313796708791260501933 5297367673765796722688225)
                  ·
                    refine ⟨3973025755324347542016169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5297367673765796722688225 3973025755324347542016169)
                    ·
                      refine ⟨2979769316493260656512127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3973025755324347542016169 2979769316493260656512127)
                      ·
                        rfl

theorem cell23_5803080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 3, 2, 2].length) (baseStart_5803080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5803080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5803080 prefixEnd_5803080 := by exact prefixLift 5803080
  have htrace : WordTrace (prefixWord ++ tailWord_5803080) baseStart_5803080 baseEnd_5803080 := by
    simpa [prefixWord, tailWord_5803080, baseEnd_5803080] using wordTrace_append hprefix tailTrace_5803080
  have hstable : (prefixWord ++ tailWord_5803080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5803080).length < 2 ^ (prefixWord ++ tailWord_5803080).sum := by decide
  have hdescent : baseEnd_5803080 < baseStart_5803080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5803080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5803090 : List Nat := [3, 2, 2, 1, 3, 1, 2, 3, 2, 4]
def baseStart_5803090 : Nat := 118140960795 + 5803090 * 2 ^ 59
def prefixEnd_5803090 : Nat := 4983230072969 + 3 ^ 40 * 5803090 * 2
def baseEnd_5803090 : Nat := 993258150433268539129027

theorem tailTrace_5803090 : CollatzResearch.WordTrace tailWord_5803090 prefixEnd_5803090 993258150433268539129027 := by
  unfold tailWord_5803090
  simp only [CollatzResearch.WordTrace]
  refine ⟨52914020136600873428123681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141104053697602329141663149 52914020136600873428123681)
  ·
    refine ⟨39685515102450655071092761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52914020136600873428123681 39685515102450655071092761)
    ·
      refine ⟨29764136326837991303319571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39685515102450655071092761 29764136326837991303319571)
      ·
        refine ⟨44646204490256986954979357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29764136326837991303319571 44646204490256986954979357)
        ·
          refine ⟨16742326683846370108117259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44646204490256986954979357 16742326683846370108117259)
          ·
            refine ⟨25113490025769555162175889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16742326683846370108117259 25113490025769555162175889)
            ·
              refine ⟨18835117519327166371631917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25113490025769555162175889 18835117519327166371631917)
              ·
                refine ⟨7063169069747687389361969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18835117519327166371631917 7063169069747687389361969)
                ·
                  refine ⟨5297376802310765542021477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7063169069747687389361969 5297376802310765542021477)
                  ·
                    refine ⟨993258150433268539129027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5297376802310765542021477 993258150433268539129027)
                    ·
                      rfl

theorem cell23_5803090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_5803090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5803090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5803090 prefixEnd_5803090 := by exact prefixLift 5803090
  have htrace : WordTrace (prefixWord ++ tailWord_5803090) baseStart_5803090 baseEnd_5803090 := by
    simpa [prefixWord, tailWord_5803090, baseEnd_5803090] using wordTrace_append hprefix tailTrace_5803090
  have hstable : (prefixWord ++ tailWord_5803090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5803090).length < 2 ^ (prefixWord ++ tailWord_5803090).sum := by decide
  have hdescent : baseEnd_5803090 < baseStart_5803090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5803090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5803093 : List Nat := [1, 3, 2, 2, 1, 2, 4, 1, 1, 2, 4]
def baseStart_5803093 : Nat := 118140960795 + 5803093 * 2 ^ 59
def prefixEnd_5803093 : Nat := 4983230072969 + 3 ^ 40 * 5803093 * 2
def baseEnd_5803093 : Nat := 2979775991741769105649567

theorem tailTrace_5803093 : CollatzResearch.WordTrace tailWord_5803093 prefixEnd_5803093 2979775991741769105649567 := by
  unfold tailWord_5803093
  simp only [CollatzResearch.WordTrace]
  refine ⟨211656189965392625224853933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141104126643595083483235955 211656189965392625224853933)
  ·
    refine ⟨79371071237022234459320225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211656189965392625224853933 79371071237022234459320225)
    ·
      refine ⟨59528303427766675844490169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79371071237022234459320225 59528303427766675844490169)
      ·
        refine ⟨44646227570825006883367627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59528303427766675844490169 44646227570825006883367627)
        ·
          refine ⟨66969341356237510325051441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44646227570825006883367627 66969341356237510325051441)
          ·
            refine ⟨50227006017178132743788581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66969341356237510325051441 50227006017178132743788581)
            ·
              refine ⟨9417563628220899889460359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50227006017178132743788581 9417563628220899889460359)
              ·
                refine ⟨14126345442331349834190539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9417563628220899889460359 14126345442331349834190539)
                ·
                  refine ⟨21189518163497024751285809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14126345442331349834190539 21189518163497024751285809)
                  ·
                    refine ⟨15892138622622768563464357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21189518163497024751285809 15892138622622768563464357)
                    ·
                      refine ⟨2979775991741769105649567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15892138622622768563464357 2979775991741769105649567)
                      ·
                        rfl

theorem cell23_5803093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_5803093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5803093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5803093 prefixEnd_5803093 := by exact prefixLift 5803093
  have htrace : WordTrace (prefixWord ++ tailWord_5803093) baseStart_5803093 baseEnd_5803093 := by
    simpa [prefixWord, tailWord_5803093, baseEnd_5803093] using wordTrace_append hprefix tailTrace_5803093
  have hstable : (prefixWord ++ tailWord_5803093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5803093).length < 2 ^ (prefixWord ++ tailWord_5803093).sum := by decide
  have hdescent : baseEnd_5803093 < baseStart_5803093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5803093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5803100 : List Nat := [2, 2, 4, 1, 1, 1, 2, 4, 1, 2, 3]
def baseStart_5803100 : Nat := 118140960795 + 5803100 * 2 ^ 59
def prefixEnd_5803100 : Nat := 4983230072969 + 3 ^ 40 * 5803100 * 2
def baseEnd_5803100 : Nat := 2979779586106350578262035

theorem tailTrace_5803100 : CollatzResearch.WordTrace tailWord_5803100 prefixEnd_5803100 2979779586106350578262035 := by
  unfold tailWord_5803100
  simp only [CollatzResearch.WordTrace]
  refine ⟨105828222638183632710179377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141104296850911510280239169 105828222638183632710179377)
  ·
    refine ⟨79371166978637724532634533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105828222638183632710179377 79371166978637724532634533)
    ·
      refine ⟨14882093808494573349868975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79371166978637724532634533 14882093808494573349868975)
      ·
        refine ⟨22323140712741860024803463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14882093808494573349868975 22323140712741860024803463)
        ·
          refine ⟨33484711069112790037205195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22323140712741860024803463 33484711069112790037205195)
          ·
            refine ⟨50227066603669185055807793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33484711069112790037205195 50227066603669185055807793)
            ·
              refine ⟨37670299952751888791855845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50227066603669185055807793 37670299952751888791855845)
              ·
                refine ⟨7063181241140979148472971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37670299952751888791855845 7063181241140979148472971)
                ·
                  refine ⟨10594771861711468722709457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7063181241140979148472971 10594771861711468722709457)
                  ·
                    refine ⟨7946078896283601542032093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10594771861711468722709457 7946078896283601542032093)
                    ·
                      refine ⟨2979779586106350578262035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7946078896283601542032093 2979779586106350578262035)
                      ·
                        rfl

theorem cell23_5803100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_5803100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5803100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5803100 prefixEnd_5803100 := by exact prefixLift 5803100
  have htrace : WordTrace (prefixWord ++ tailWord_5803100) baseStart_5803100 baseEnd_5803100 := by
    simpa [prefixWord, tailWord_5803100, baseEnd_5803100] using wordTrace_append hprefix tailTrace_5803100
  have hstable : (prefixWord ++ tailWord_5803100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5803100).length < 2 ^ (prefixWord ++ tailWord_5803100).sum := by decide
  have hdescent : baseEnd_5803100 < baseStart_5803100 := by decide
  rcases family_descends (prefixWord ++ tailWord_5803100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5803101 : List Nat := [1, 4, 4, 1, 3, 1, 1, 1, 2, 3, 2]
def baseStart_5803101 : Nat := 118140960795 + 5803101 * 2 ^ 59
def prefixEnd_5803101 : Nat := 4983230072969 + 3 ^ 40 * 5803101 * 2
def baseEnd_5803101 : Nat := 2979780099587005074349531

theorem tailTrace_5803101 : CollatzResearch.WordTrace tailWord_5803101 prefixEnd_5803101 2979780099587005074349531 := by
  unfold tailWord_5803101
  simp only [CollatzResearch.WordTrace]
  refine ⟨211656481749363642591145157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141104321166242428394096771 211656481749363642591145157)
  ·
    refine ⟨39685590328005682985839717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 211656481749363642591145157 39685590328005682985839717)
    ·
      refine ⟨7441048186501065559844947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39685590328005682985839717 7441048186501065559844947)
      ·
        refine ⟨11161572279751598339767421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7441048186501065559844947 11161572279751598339767421)
        ·
          refine ⟨4185589604906849377412783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11161572279751598339767421 4185589604906849377412783)
          ·
            refine ⟨6278384407360274066119175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4185589604906849377412783 6278384407360274066119175)
            ·
              refine ⟨9417576611040411099178763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6278384407360274066119175 9417576611040411099178763)
              ·
                refine ⟨14126364916560616648768145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9417576611040411099178763 14126364916560616648768145)
                ·
                  refine ⟨10594773687420462486576109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14126364916560616648768145 10594773687420462486576109)
                  ·
                    refine ⟨3973040132782673432466041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10594773687420462486576109 3973040132782673432466041)
                    ·
                      refine ⟨2979780099587005074349531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3973040132782673432466041 2979780099587005074349531)
                      ·
                        rfl

theorem cell23_5803101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_5803101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5803101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5803101 prefixEnd_5803101 := by exact prefixLift 5803101
  have htrace : WordTrace (prefixWord ++ tailWord_5803101) baseStart_5803101 baseEnd_5803101 := by
    simpa [prefixWord, tailWord_5803101, baseEnd_5803101] using wordTrace_append hprefix tailTrace_5803101
  have hstable : (prefixWord ++ tailWord_5803101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5803101).length < 2 ^ (prefixWord ++ tailWord_5803101).sum := by decide
  have hdescent : baseEnd_5803101 < baseStart_5803101 := by decide
  rcases family_descends (prefixWord ++ tailWord_5803101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5803113 : List Nat := [1, 2, 1, 1, 1, 6, 2, 2, 1, 3, 3]
def baseStart_5803113 : Nat := 118140960795 + 5803113 * 2 ^ 59
def prefixEnd_5803113 : Nat := 4983230072969 + 3 ^ 40 * 5803113 * 2
def baseEnd_5803113 : Nat := 2979786261354859027399475

theorem tailTrace_5803113 : CollatzResearch.WordTrace tailWord_5803113 prefixEnd_5803113 2979786261354859027399475 := by
  unfold tailWord_5803113
  simp only [CollatzResearch.WordTrace]
  refine ⟨211656919425320168640581993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141104612950213445760387995 211656919425320168640581993)
  ·
    refine ⟨158742689568990126480436495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211656919425320168640581993 158742689568990126480436495)
    ·
      refine ⟨238114034353485189720654743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158742689568990126480436495 238114034353485189720654743)
      ·
        refine ⟨357171051530227784580982115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238114034353485189720654743 357171051530227784580982115)
        ·
          refine ⟨535756577295341676871473173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357171051530227784580982115 535756577295341676871473173)
          ·
            refine ⟨25113589560719141103350305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 535756577295341676871473173 25113589560719141103350305)
            ·
              refine ⟨18835192170539355827512729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25113589560719141103350305 18835192170539355827512729)
              ·
                refine ⟨14126394127904516870634547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18835192170539355827512729 14126394127904516870634547)
                ·
                  refine ⟨21189591191856775305951821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14126394127904516870634547 21189591191856775305951821)
                  ·
                    refine ⟨7946096696946290739731933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21189591191856775305951821 7946096696946290739731933)
                    ·
                      refine ⟨2979786261354859027399475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7946096696946290739731933 2979786261354859027399475)
                      ·
                        rfl

theorem cell23_5803113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 3, 3].length) (baseStart_5803113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5803113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5803113 prefixEnd_5803113 := by exact prefixLift 5803113
  have htrace : WordTrace (prefixWord ++ tailWord_5803113) baseStart_5803113 baseEnd_5803113 := by
    simpa [prefixWord, tailWord_5803113, baseEnd_5803113] using wordTrace_append hprefix tailTrace_5803113
  have hstable : (prefixWord ++ tailWord_5803113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5803113).length < 2 ^ (prefixWord ++ tailWord_5803113).sum := by decide
  have hdescent : baseEnd_5803113 < baseStart_5803113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5803113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5803114 : List Nat := [3, 1, 3, 2, 2, 1, 1, 5, 1, 2, 2]
def baseStart_5803114 : Nat := 118140960795 + 5803114 * 2 ^ 59
def prefixEnd_5803114 : Nat := 4983230072969 + 3 ^ 40 * 5803114 * 2
def baseEnd_5803114 : Nat := 2979786774835513523486971

theorem tailTrace_5803114 : CollatzResearch.WordTrace tailWord_5803114 prefixEnd_5803114 2979786774835513523486971 := by
  unfold tailWord_5803114
  simp only [CollatzResearch.WordTrace]
  refine ⟨52914238974579136452842099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141104637265544363874245597 52914238974579136452842099)
  ·
    refine ⟨79371358461868704679263149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52914238974579136452842099 79371358461868704679263149)
    ·
      refine ⟨29764259423200764254723681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79371358461868704679263149 29764259423200764254723681)
      ·
        refine ⟨22323194567400573191042761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29764259423200764254723681 22323194567400573191042761)
        ·
          refine ⟨16742395925550429893282071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22323194567400573191042761 16742395925550429893282071)
          ·
            refine ⟨25113593888325644839923107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16742395925550429893282071 25113593888325644839923107)
            ·
              refine ⟨37670390832488467259884661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25113593888325644839923107 37670390832488467259884661)
              ·
                refine ⟨3531599140545793805614187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37670390832488467259884661 3531599140545793805614187)
                ·
                  refine ⟨5297398710818690708421281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3531599140545793805614187 5297398710818690708421281)
                  ·
                    refine ⟨3973049033114018031315961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5297398710818690708421281 3973049033114018031315961)
                    ·
                      refine ⟨2979786774835513523486971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3973049033114018031315961 2979786774835513523486971)
                      ·
                        rfl

theorem cell23_5803114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_5803114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5803114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5803114 prefixEnd_5803114 := by exact prefixLift 5803114
  have htrace : WordTrace (prefixWord ++ tailWord_5803114) baseStart_5803114 baseEnd_5803114 := by
    simpa [prefixWord, tailWord_5803114, baseEnd_5803114] using wordTrace_append hprefix tailTrace_5803114
  have hstable : (prefixWord ++ tailWord_5803114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5803114).length < 2 ^ (prefixWord ++ tailWord_5803114).sum := by decide
  have hdescent : baseEnd_5803114 < baseStart_5803114 := by decide
  rcases family_descends (prefixWord ++ tailWord_5803114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5803117 : List Nat := [1, 5, 1, 1, 2, 2, 4, 1, 1, 2, 3]
def baseStart_5803117 : Nat := 118140960795 + 5803117 * 2 ^ 59
def prefixEnd_5803117 : Nat := 4983230072969 + 3 ^ 40 * 5803117 * 2
def baseEnd_5803117 : Nat := 2979788315277477011749457

theorem tailTrace_5803117 : CollatzResearch.WordTrace tailWord_5803117 prefixEnd_5803117 2979788315277477011749457 := by
  unfold tailWord_5803117
  simp only [CollatzResearch.WordTrace]
  refine ⟨211657065317305677323727605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141104710211537118215818403 211657065317305677323727605)
  ·
    refine ⟨19842849873497407249099463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 211657065317305677323727605 19842849873497407249099463)
    ·
      refine ⟨29764274810246110873649195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19842849873497407249099463 29764274810246110873649195)
      ·
        refine ⟨44646412215369166310473793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29764274810246110873649195 44646412215369166310473793)
        ·
          refine ⟨33484809161526874732855345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44646412215369166310473793 33484809161526874732855345)
          ·
            refine ⟨25113606871145156049641509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33484809161526874732855345 25113606871145156049641509)
            ·
              refine ⟨4708801288339716759307783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25113606871145156049641509 4708801288339716759307783)
              ·
                refine ⟨7063201932509575138961675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4708801288339716759307783 7063201932509575138961675)
                ·
                  refine ⟨10594802898764362708442513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7063201932509575138961675 10594802898764362708442513)
                  ·
                    refine ⟨7946102174073272031331885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10594802898764362708442513 7946102174073272031331885)
                    ·
                      refine ⟨2979788315277477011749457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7946102174073272031331885 2979788315277477011749457)
                      ·
                        rfl

theorem cell23_5803117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 1, 1, 2, 3].length) (baseStart_5803117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5803117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5803117 prefixEnd_5803117 := by exact prefixLift 5803117
  have htrace : WordTrace (prefixWord ++ tailWord_5803117) baseStart_5803117 baseEnd_5803117 := by
    simpa [prefixWord, tailWord_5803117, baseEnd_5803117] using wordTrace_append hprefix tailTrace_5803117
  have hstable : (prefixWord ++ tailWord_5803117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5803117).length < 2 ^ (prefixWord ++ tailWord_5803117).sum := by decide
  have hdescent : baseEnd_5803117 < baseStart_5803117 := by decide
  rcases family_descends (prefixWord ++ tailWord_5803117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5803134 : List Nat := [4, 2, 4, 1, 1, 1, 1, 2, 1, 1, 5]
def baseStart_5803134 : Nat := 118140960795 + 5803134 * 2 ^ 59
def prefixEnd_5803134 : Nat := 4983230072969 + 3 ^ 40 * 5803134 * 2
def baseEnd_5803134 : Nat := 2979797044448603445236879

theorem tailTrace_5803134 : CollatzResearch.WordTrace tailWord_5803134 prefixEnd_5803134 2979797044448603445236879 := by
  unfold tailWord_5803134
  simp only [CollatzResearch.WordTrace]
  refine ⟨26457210669780511153387057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141105123572162726151397637 26457210669780511153387057)
  ·
    refine ⟨19842908002335383365040293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26457210669780511153387057 19842908002335383365040293)
    ·
      refine ⟨3720545250437884380945055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19842908002335383365040293 3720545250437884380945055)
      ·
        refine ⟨5580817875656826571417583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3720545250437884380945055 5580817875656826571417583)
        ·
          refine ⟨8371226813485239857126375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5580817875656826571417583 8371226813485239857126375)
          ·
            refine ⟨12556840220227859785689563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8371226813485239857126375 12556840220227859785689563)
            ·
              refine ⟨18835260330341789678534345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12556840220227859785689563 18835260330341789678534345)
              ·
                refine ⟨14126445247756342258900759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18835260330341789678534345 14126445247756342258900759)
                ·
                  refine ⟨21189667871634513388351139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14126445247756342258900759 21189667871634513388351139)
                  ·
                    refine ⟨31784501807451770082526709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21189667871634513388351139 31784501807451770082526709)
                    ·
                      refine ⟨2979797044448603445236879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31784501807451770082526709 2979797044448603445236879)
                      ·
                        rfl

theorem cell23_5803134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_5803134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5803134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5803134 prefixEnd_5803134 := by exact prefixLift 5803134
  have htrace : WordTrace (prefixWord ++ tailWord_5803134) baseStart_5803134 baseEnd_5803134 := by
    simpa [prefixWord, tailWord_5803134, baseEnd_5803134] using wordTrace_append hprefix tailTrace_5803134
  have hstable : (prefixWord ++ tailWord_5803134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5803134).length < 2 ^ (prefixWord ++ tailWord_5803134).sum := by decide
  have hdescent : baseEnd_5803134 < baseStart_5803134 := by decide
  rcases family_descends (prefixWord ++ tailWord_5803134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5803136 : List Nat := [2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 4]
def baseStart_5803136 : Nat := 118140960795 + 5803136 * 2 ^ 59
def prefixEnd_5803136 : Nat := 4983230072969 + 3 ^ 40 * 5803136 * 2
def baseEnd_5803136 : Nat := 2979798071409912437411869

theorem tailTrace_5803136 : CollatzResearch.WordTrace tailWord_5803136 prefixEnd_5803136 2979798071409912437411869 := by
  unfold tailWord_5803136
  simp only [CollatzResearch.WordTrace]
  refine ⟨105828879152118421784334631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141105172202824562379112841 105828879152118421784334631)
  ·
    refine ⟨158743318728177632676501947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105828879152118421784334631 158743318728177632676501947)
    ·
      refine ⟨238114978092266449014752921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158743318728177632676501947 238114978092266449014752921)
      ·
        refine ⟨178586233569199836761064691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238114978092266449014752921 178586233569199836761064691)
        ·
          refine ⟨267879350353799755141597037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178586233569199836761064691 267879350353799755141597037)
          ·
            refine ⟨100454756382674908178098889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 267879350353799755141597037 100454756382674908178098889)
            ·
              refine ⟨75341067287006181133574167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100454756382674908178098889 75341067287006181133574167)
              ·
                refine ⟨113011600930509271700361251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75341067287006181133574167 113011600930509271700361251)
                ·
                  refine ⟨169517401395763907550541877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113011600930509271700361251 169517401395763907550541877)
                  ·
                    refine ⟨15892256380852866332863301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 169517401395763907550541877 15892256380852866332863301)
                    ·
                      refine ⟨2979798071409912437411869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15892256380852866332863301 2979798071409912437411869)
                      ·
                        rfl

theorem cell23_5803136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 4].length) (baseStart_5803136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5803136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5803136 prefixEnd_5803136 := by exact prefixLift 5803136
  have htrace : WordTrace (prefixWord ++ tailWord_5803136) baseStart_5803136 baseEnd_5803136 := by
    simpa [prefixWord, tailWord_5803136, baseEnd_5803136] using wordTrace_append hprefix tailTrace_5803136
  have hstable : (prefixWord ++ tailWord_5803136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5803136).length < 2 ^ (prefixWord ++ tailWord_5803136).sum := by decide
  have hdescent : baseEnd_5803136 < baseStart_5803136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5803136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5803173 : List Nat := [1, 3, 1, 2, 1, 5, 1, 1, 2, 1, 5]
def baseStart_5803173 : Nat := 118140960795 + 5803173 * 2 ^ 59
def prefixEnd_5803173 : Nat := 4983230072969 + 3 ^ 40 * 5803173 * 2
def baseEnd_5803173 : Nat := 2979817070194128792649199

theorem tailTrace_5803173 : CollatzResearch.WordTrace tailWord_5803173 prefixEnd_5803173 2979817070194128792649199 := by
  unfold tailWord_5803173
  simp only [CollatzResearch.WordTrace]
  refine ⟨211659107805102798887766173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141106071870068532591844115 211659107805102798887766173)
  ·
    refine ⟨79372165426913549582912315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211659107805102798887766173 79372165426913549582912315)
    ·
      refine ⟨119058248140370324374368473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79372165426913549582912315 119058248140370324374368473)
      ·
        refine ⟨89293686105277743280776355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119058248140370324374368473 89293686105277743280776355)
        ·
          refine ⟨133940529157916614921164533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89293686105277743280776355 133940529157916614921164533)
          ·
            refine ⟨12556924608554682648859175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 133940529157916614921164533 12556924608554682648859175)
            ·
              refine ⟨18835386912832023973288763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12556924608554682648859175 18835386912832023973288763)
              ·
                refine ⟨28253080369248035959933145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18835386912832023973288763 28253080369248035959933145)
                ·
                  refine ⟨21189810276936026969949859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28253080369248035959933145 21189810276936026969949859)
                  ·
                    refine ⟨31784715415404040454924789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21189810276936026969949859 31784715415404040454924789)
                    ·
                      refine ⟨2979817070194128792649199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31784715415404040454924789 2979817070194128792649199)
                      ·
                        rfl

theorem cell23_5803173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_5803173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5803173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5803173 prefixEnd_5803173 := by exact prefixLift 5803173
  have htrace : WordTrace (prefixWord ++ tailWord_5803173) baseStart_5803173 baseEnd_5803173 := by
    simpa [prefixWord, tailWord_5803173, baseEnd_5803173] using wordTrace_append hprefix tailTrace_5803173
  have hstable : (prefixWord ++ tailWord_5803173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5803173).length < 2 ^ (prefixWord ++ tailWord_5803173).sum := by decide
  have hdescent : baseEnd_5803173 < baseStart_5803173 := by decide
  rcases family_descends (prefixWord ++ tailWord_5803173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5803193 : List Nat := [1, 2, 1, 4, 1, 3, 3, 1, 7]
def baseStart_5803193 : Nat := 118140960795 + 5803193 * 2 ^ 59
def prefixEnd_5803193 : Nat := 4983230072969 + 3 ^ 40 * 5803193 * 2
def baseEnd_5803193 : Nat := 331091926645246523822123

theorem tailTrace_5803193 : CollatzResearch.WordTrace tailWord_5803193 prefixEnd_5803193 331091926645246523822123 := by
  unfold tailWord_5803193
  simp only [CollatzResearch.WordTrace]
  refine ⟨211659837265030342303494233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141106558176686894868996155 211659837265030342303494233)
  ·
    refine ⟨158744877948772756727620675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211659837265030342303494233 158744877948772756727620675)
    ·
      refine ⟨238117316923159135091431013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158744877948772756727620675 238117316923159135091431013)
      ·
        refine ⟨44646996923092337829643315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 238117316923159135091431013 44646996923092337829643315)
        ·
          refine ⟨66970495384638506744464973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44646996923092337829643315 66970495384638506744464973)
          ·
            refine ⟨25113935769239440029174365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66970495384638506744464973 25113935769239440029174365)
            ·
              refine ⟨9417725913464790010940387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25113935769239440029174365 9417725913464790010940387)
              ·
                refine ⟨14126588870197185016410581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9417725913464790010940387 14126588870197185016410581)
                ·
                  refine ⟨331091926645246523822123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14126588870197185016410581 331091926645246523822123)
                  ·
                    rfl

theorem cell23_5803193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 7].length) (baseStart_5803193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5803193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5803193 prefixEnd_5803193 := by exact prefixLift 5803193
  have htrace : WordTrace (prefixWord ++ tailWord_5803193) baseStart_5803193 baseEnd_5803193 := by
    simpa [prefixWord, tailWord_5803193, baseEnd_5803193] using wordTrace_append hprefix tailTrace_5803193
  have hstable : (prefixWord ++ tailWord_5803193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5803193).length < 2 ^ (prefixWord ++ tailWord_5803193).sum := by decide
  have hdescent : baseEnd_5803193 < baseStart_5803193 := by decide
  rcases family_descends (prefixWord ++ tailWord_5803193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5803223 : List Nat := [1, 1, 3, 2, 1, 2, 3, 3, 2, 5]
def baseStart_5803223 : Nat := 118140960795 + 5803223 * 2 ^ 59
def prefixEnd_5803223 : Nat := 4983230072969 + 3 ^ 40 * 5803223 * 2
def baseEnd_5803223 : Nat := 993280914742284532341323

theorem tailTrace_5803223 : CollatzResearch.WordTrace tailWord_5803223 prefixEnd_5803223 993280914742284532341323 := by
  unfold tailWord_5803223
  simp only [CollatzResearch.WordTrace]
  refine ⟨211660931454921657427086323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141107287636614438284724215 211660931454921657427086323)
  ·
    refine ⟨317491397182382486140629485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211660931454921657427086323 317491397182382486140629485)
    ·
      refine ⟨119059273943393432302736057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 317491397182382486140629485 119059273943393432302736057)
      ·
        refine ⟨89294455457545074227052043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119059273943393432302736057 89294455457545074227052043)
        ·
          refine ⟨133941683186317611340578065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89294455457545074227052043 133941683186317611340578065)
          ·
            refine ⟨100456262389738208505433549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133941683186317611340578065 100456262389738208505433549)
            ·
              refine ⟨37671098396151828189537581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100456262389738208505433549 37671098396151828189537581)
              ·
                refine ⟨14126661898556935571076593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37671098396151828189537581 14126661898556935571076593)
                ·
                  refine ⟨10594996423917701678307445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14126661898556935571076593 10594996423917701678307445)
                  ·
                    refine ⟨993280914742284532341323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10594996423917701678307445 993280914742284532341323)
                    ·
                      rfl

theorem cell23_5803223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 2, 5].length) (baseStart_5803223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5803223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5803223 prefixEnd_5803223 := by exact prefixLift 5803223
  have htrace : WordTrace (prefixWord ++ tailWord_5803223) baseStart_5803223 baseEnd_5803223 := by
    simpa [prefixWord, tailWord_5803223, baseEnd_5803223] using wordTrace_append hprefix tailTrace_5803223
  have hstable : (prefixWord ++ tailWord_5803223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5803223).length < 2 ^ (prefixWord ++ tailWord_5803223).sum := by decide
  have hdescent : baseEnd_5803223 < baseStart_5803223 := by decide
  rcases family_descends (prefixWord ++ tailWord_5803223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5803233 : List Nat := [1, 2, 3, 1, 3, 2, 1, 2, 1, 2, 5]
def baseStart_5803233 : Nat := 118140960795 + 5803233 * 2 ^ 59
def prefixEnd_5803233 : Nat := 4983230072969 + 3 ^ 40 * 5803233 * 2
def baseEnd_5803233 : Nat := 2979847879033398557898923

theorem tailTrace_5803233 : CollatzResearch.WordTrace tailWord_5803233 prefixEnd_5803233 2979847879033398557898923 := by
  unfold tailWord_5803233
  simp only [CollatzResearch.WordTrace]
  refine ⟨211661296184885429134950353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141107530789923619423300235 211661296184885429134950353)
  ·
    refine ⟨158745972138664071851212765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211661296184885429134950353 158745972138664071851212765)
    ·
      refine ⟨59529739551999026944204787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158745972138664071851212765 59529739551999026944204787)
      ·
        refine ⟨89294609327998540416307181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59529739551999026944204787 89294609327998540416307181)
        ·
          refine ⟨33485478497999452656115193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89294609327998540416307181 33485478497999452656115193)
          ·
            refine ⟨25114108873499589492086395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33485478497999452656115193 25114108873499589492086395)
            ·
              refine ⟨37671163310249384238129593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25114108873499589492086395 37671163310249384238129593)
              ·
                refine ⟨28253372482687038178597195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37671163310249384238129593 28253372482687038178597195)
                ·
                  refine ⟨42380058724030557267895793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28253372482687038178597195 42380058724030557267895793)
                  ·
                    refine ⟨31785044043022917950921845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42380058724030557267895793 31785044043022917950921845)
                    ·
                      refine ⟨2979847879033398557898923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31785044043022917950921845 2979847879033398557898923)
                      ·
                        rfl

theorem cell23_5803233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_5803233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5803233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5803233 prefixEnd_5803233 := by exact prefixLift 5803233
  have htrace : WordTrace (prefixWord ++ tailWord_5803233) baseStart_5803233 baseEnd_5803233 := by
    simpa [prefixWord, tailWord_5803233, baseEnd_5803233] using wordTrace_append hprefix tailTrace_5803233
  have hstable : (prefixWord ++ tailWord_5803233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5803233).length < 2 ^ (prefixWord ++ tailWord_5803233).sum := by decide
  have hdescent : baseEnd_5803233 < baseStart_5803233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5803233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5803304 : List Nat := [2, 1, 5, 1, 2, 1, 2, 4, 1, 4]
def baseStart_5803304 : Nat := 118140960795 + 5803304 * 2 ^ 59
def prefixEnd_5803304 : Nat := 4983230072969 + 3 ^ 40 * 5803304 * 2
def baseEnd_5803304 : Nat := 993294778719955926703699

theorem tailTrace_5803304 : CollatzResearch.WordTrace tailWord_5803304 prefixEnd_5803304 993294778719955926703699 := by
  unfold tailWord_5803304
  simp only [CollatzResearch.WordTrace]
  refine ⟨105831942883814104130392483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141109257178418805507189977 105831942883814104130392483)
  ·
    refine ⟨158747914325721156195588725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105831942883814104130392483 158747914325721156195588725)
    ·
      refine ⟨14882616968036358393336443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 158747914325721156195588725 14882616968036358393336443)
      ·
        refine ⟨22323925452054537590004665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14882616968036358393336443 22323925452054537590004665)
        ·
          refine ⟨16742944089040903192503499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22323925452054537590004665 16742944089040903192503499)
          ·
            refine ⟨25114416133561354788755249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16742944089040903192503499 25114416133561354788755249)
            ·
              refine ⟨18835812100171016091566437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25114416133561354788755249 18835812100171016091566437)
              ·
                refine ⟨3531714768782065517168707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18835812100171016091566437 3531714768782065517168707)
                ·
                  refine ⟨5297572153173098275753061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3531714768782065517168707 5297572153173098275753061)
                  ·
                    refine ⟨993294778719955926703699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5297572153173098275753061 993294778719955926703699)
                    ·
                      rfl

theorem cell23_5803304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_5803304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5803304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5803304 prefixEnd_5803304 := by exact prefixLift 5803304
  have htrace : WordTrace (prefixWord ++ tailWord_5803304) baseStart_5803304 baseEnd_5803304 := by
    simpa [prefixWord, tailWord_5803304, baseEnd_5803304] using wordTrace_append hprefix tailTrace_5803304
  have hstable : (prefixWord ++ tailWord_5803304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5803304).length < 2 ^ (prefixWord ++ tailWord_5803304).sum := by decide
  have hdescent : baseEnd_5803304 < baseStart_5803304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5803304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5803317 : List Nat := [1, 3, 3, 1, 2, 3, 3, 1, 6]
def baseStart_5803317 : Nat := 118140960795 + 5803317 * 2 ^ 59
def prefixEnd_5803317 : Nat := 4983230072969 + 3 ^ 40 * 5803317 * 2
def baseEnd_5803317 : Nat := 331099001267597358805393

theorem tailTrace_5803317 : CollatzResearch.WordTrace tailWord_5803317 prefixEnd_5803317 331099001267597358805393 := by
  unfold tailWord_5803317
  simp only [CollatzResearch.WordTrace]
  refine ⟨211664359916581111481008205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141109573277720740987338803 211664359916581111481008205)
  ·
    refine ⟨79374134968717916805378077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211664359916581111481008205 79374134968717916805378077)
    ·
      refine ⟨29765300613269218802016779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79374134968717916805378077 29765300613269218802016779)
      ·
        refine ⟨44647950919903828203025169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29765300613269218802016779 44647950919903828203025169)
        ·
          refine ⟨33485963189927871152268877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44647950919903828203025169 33485963189927871152268877)
          ·
            refine ⟨12557236196222951682100829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33485963189927871152268877 12557236196222951682100829)
            ·
              refine ⟨4708963573583606880787811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12557236196222951682100829 4708963573583606880787811)
              ·
                refine ⟨7063445360375410321181717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4708963573583606880787811 7063445360375410321181717)
                ·
                  refine ⟨331099001267597358805393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7063445360375410321181717 331099001267597358805393)
                  ·
                    rfl

theorem cell23_5803317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 1, 6].length) (baseStart_5803317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5803317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5803317 prefixEnd_5803317 := by exact prefixLift 5803317
  have htrace : WordTrace (prefixWord ++ tailWord_5803317) baseStart_5803317 baseEnd_5803317 := by
    simpa [prefixWord, tailWord_5803317, baseEnd_5803317] using wordTrace_append hprefix tailTrace_5803317
  have hstable : (prefixWord ++ tailWord_5803317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5803317).length < 2 ^ (prefixWord ++ tailWord_5803317).sum := by decide
  have hdescent : baseEnd_5803317 < baseStart_5803317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5803317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5803327 : List Nat := [1, 1, 2, 2, 4, 2, 2, 2, 3, 1, 3]
def baseStart_5803327 : Nat := 118140960795 + 5803327 * 2 ^ 59
def prefixEnd_5803327 : Nat := 4983230072969 + 3 ^ 40 * 5803327 * 2
def baseEnd_5803327 : Nat := 2979896146214921190123491

theorem tailTrace_5803327 : CollatzResearch.WordTrace tailWord_5803327 prefixEnd_5803327 2979896146214921190123491 := by
  unfold tailWord_5803327
  simp only [CollatzResearch.WordTrace]
  refine ⟨211664724646544883188872235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141109816431029922125914823 211664724646544883188872235)
  ·
    refine ⟨317497086969817324783308353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211664724646544883188872235 317497086969817324783308353)
    ·
      refine ⟨238122815227362993587481265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317497086969817324783308353 238122815227362993587481265)
      ·
        refine ⟨178592111420522245190610949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238122815227362993587481265 178592111420522245190610949)
        ·
          refine ⟨33486020891347920973239553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 178592111420522245190610949 33486020891347920973239553)
          ·
            refine ⟨25114515668510940729929665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33486020891347920973239553 25114515668510940729929665)
            ·
              refine ⟨18835886751383205547447249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25114515668510940729929665 18835886751383205547447249)
              ·
                refine ⟨14126915063537404160585437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18835886751383205547447249 14126915063537404160585437)
                ·
                  refine ⟨5297593148826526560219539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14126915063537404160585437 5297593148826526560219539)
                  ·
                    refine ⟨7946389723239789840329309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5297593148826526560219539 7946389723239789840329309)
                    ·
                      refine ⟨2979896146214921190123491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7946389723239789840329309 2979896146214921190123491)
                      ·
                        rfl

theorem cell23_5803327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 3, 1, 3].length) (baseStart_5803327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5803327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5803327 prefixEnd_5803327 := by exact prefixLift 5803327
  have htrace : WordTrace (prefixWord ++ tailWord_5803327) baseStart_5803327 baseEnd_5803327 := by
    simpa [prefixWord, tailWord_5803327, baseEnd_5803327] using wordTrace_append hprefix tailTrace_5803327
  have hstable : (prefixWord ++ tailWord_5803327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5803327).length < 2 ^ (prefixWord ++ tailWord_5803327).sum := by decide
  have hdescent : baseEnd_5803327 < baseStart_5803327 := by decide
  rcases family_descends (prefixWord ++ tailWord_5803327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5803333 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 2, 5, 4]
def baseStart_5803333 : Nat := 118140960795 + 5803333 * 2 ^ 59
def prefixEnd_5803333 : Nat := 4983230072969 + 3 ^ 40 * 5803333 * 2
def baseEnd_5803333 : Nat := 2979899227098848166648463

theorem tailTrace_5803333 : CollatzResearch.WordTrace tailWord_5803333 prefixEnd_5803333 2979899227098848166648463 := by
  unfold tailWord_5803333
  simp only [CollatzResearch.WordTrace]
  refine ⟨211664943484523146213590653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141109962323015430809060435 211664943484523146213590653)
  ·
    refine ⟨79374353806696179830096495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211664943484523146213590653 79374353806696179830096495)
    ·
      refine ⟨119061530710044269745144743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79374353806696179830096495 119061530710044269745144743)
      ·
        refine ⟨178592296065066404617717115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119061530710044269745144743 178592296065066404617717115)
        ·
          refine ⟨267888444097599606926575673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178592296065066404617717115 267888444097599606926575673)
          ·
            refine ⟨200916333073199705194931755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267888444097599606926575673 200916333073199705194931755)
            ·
              refine ⟨301374499609799557792397633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200916333073199705194931755 301374499609799557792397633)
              ·
                refine ⟨226030874707349668344298225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 301374499609799557792397633 226030874707349668344298225)
                ·
                  refine ⟨169523156030512251258223669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 226030874707349668344298225 169523156030512251258223669)
                  ·
                    refine ⟨15892795877860523555458469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 169523156030512251258223669 15892795877860523555458469)
                    ·
                      refine ⟨2979899227098848166648463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15892795877860523555458469 2979899227098848166648463)
                      ·
                        rfl

theorem cell23_5803333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 5, 4].length) (baseStart_5803333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5803333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5803333 prefixEnd_5803333 := by exact prefixLift 5803333
  have htrace : WordTrace (prefixWord ++ tailWord_5803333) baseStart_5803333 baseEnd_5803333 := by
    simpa [prefixWord, tailWord_5803333, baseEnd_5803333] using wordTrace_append hprefix tailTrace_5803333
  have hstable : (prefixWord ++ tailWord_5803333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5803333).length < 2 ^ (prefixWord ++ tailWord_5803333).sum := by decide
  have hdescent : baseEnd_5803333 < baseStart_5803333 := by decide
  rcases family_descends (prefixWord ++ tailWord_5803333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5803381 : List Nat := [1, 3, 4, 1, 4, 1, 1, 2, 1, 5]
def baseStart_5803381 : Nat := 118140960795 + 5803381 * 2 ^ 59
def prefixEnd_5803381 : Nat := 4983230072969 + 3 ^ 40 * 5803381 * 2
def baseEnd_5803381 : Nat := 993307958056754659616081

theorem tailTrace_5803381 : CollatzResearch.WordTrace tailWord_5803381 prefixEnd_5803381 993307958056754659616081 := by
  unfold tailWord_5803381
  simp only [CollatzResearch.WordTrace]
  refine ⟨211666694188349250411337997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141111129458899500274225331 211666694188349250411337997)
  ·
    refine ⟨79375010320630968904251749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211666694188349250411337997 79375010320630968904251749)
    ·
      refine ⟨14882814435118306669547203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79375010320630968904251749 14882814435118306669547203)
      ·
        refine ⟨22324221652677460004320805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14882814435118306669547203 22324221652677460004320805)
        ·
          refine ⟨4185791559877023750810151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22324221652677460004320805 4185791559877023750810151)
          ·
            refine ⟨6278687339815535626215227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4185791559877023750810151 6278687339815535626215227)
            ·
              refine ⟨9418031009723303439322841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6278687339815535626215227 9418031009723303439322841)
              ·
                refine ⟨7063523257292477579492131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9418031009723303439322841 7063523257292477579492131)
                ·
                  refine ⟨10595284885938716369238197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7063523257292477579492131 10595284885938716369238197)
                  ·
                    refine ⟨993307958056754659616081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10595284885938716369238197 993307958056754659616081)
                    ·
                      rfl

theorem cell23_5803381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_5803381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5803381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5803381 prefixEnd_5803381 := by exact prefixLift 5803381
  have htrace : WordTrace (prefixWord ++ tailWord_5803381) baseStart_5803381 baseEnd_5803381 := by
    simpa [prefixWord, tailWord_5803381, baseEnd_5803381] using wordTrace_append hprefix tailTrace_5803381
  have hstable : (prefixWord ++ tailWord_5803381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5803381).length < 2 ^ (prefixWord ++ tailWord_5803381).sum := by decide
  have hdescent : baseEnd_5803381 < baseStart_5803381 := by decide
  rcases family_descends (prefixWord ++ tailWord_5803381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5803394 : List Nat := [3, 4, 2, 1, 1, 2, 1, 2, 1, 6]
def baseStart_5803394 : Nat := 118140960795 + 5803394 * 2 ^ 59
def prefixEnd_5803394 : Nat := 4983230072969 + 3 ^ 40 * 5803394 * 2
def baseEnd_5803394 : Nat := 993310183139590809328561

theorem tailTrace_5803394 : CollatzResearch.WordTrace tailWord_5803394 prefixEnd_5803394 993310183139590809328561 := by
  unfold tailWord_5803394
  simp only [CollatzResearch.WordTrace]
  refine ⟨52916792084325538407890309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141111445558201435754374157 52916792084325538407890309)
  ·
    refine ⟨9921898515811038451479433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52916792084325538407890309 9921898515811038451479433)
    ·
      refine ⟨7441423886858278838609575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9921898515811038451479433 7441423886858278838609575)
      ·
        refine ⟨11162135830287418257914363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7441423886858278838609575 11162135830287418257914363)
        ·
          refine ⟨16743203745431127386871545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11162135830287418257914363 16743203745431127386871545)
          ·
            refine ⟨12557402809073345540153659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16743203745431127386871545 12557402809073345540153659)
            ·
              refine ⟨18836104213610018310230489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12557402809073345540153659 18836104213610018310230489)
              ·
                refine ⟨14127078160207513732672867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18836104213610018310230489 14127078160207513732672867)
                ·
                  refine ⟨21190617240311270599009301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14127078160207513732672867 21190617240311270599009301)
                  ·
                    refine ⟨993310183139590809328561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21190617240311270599009301 993310183139590809328561)
                    ·
                      rfl

theorem cell23_5803394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_5803394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5803394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5803394 prefixEnd_5803394 := by exact prefixLift 5803394
  have htrace : WordTrace (prefixWord ++ tailWord_5803394) baseStart_5803394 baseEnd_5803394 := by
    simpa [prefixWord, tailWord_5803394, baseEnd_5803394] using wordTrace_append hprefix tailTrace_5803394
  have hstable : (prefixWord ++ tailWord_5803394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5803394).length < 2 ^ (prefixWord ++ tailWord_5803394).sum := by decide
  have hdescent : baseEnd_5803394 < baseStart_5803394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5803394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5803404 : List Nat := [2, 2, 1, 2, 1, 3, 5, 1, 1, 2, 3]
def baseStart_5803404 : Nat := 118140960795 + 5803404 * 2 ^ 59
def prefixEnd_5803404 : Nat := 4983230072969 + 3 ^ 40 * 5803404 * 2
def baseEnd_5803404 : Nat := 2979935684225317388860637

theorem tailTrace_5803404 : CollatzResearch.WordTrace tailWord_5803404 prefixEnd_5803404 2979935684225317388860637 := by
  unfold tailWord_5803404
  simp only [CollatzResearch.WordTrace]
  refine ⟨105833766533632962669712633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141111688711510616892950177 105833766533632962669712633)
  ·
    refine ⟨79375324900224722002284475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105833766533632962669712633 79375324900224722002284475)
    ·
      refine ⟨119062987350337083003426713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79375324900224722002284475 119062987350337083003426713)
      ·
        refine ⟨89297240512752812252570035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119062987350337083003426713 89297240512752812252570035)
        ·
          refine ⟨133945860769129218378855053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89297240512752812252570035 133945860769129218378855053)
          ·
            refine ⟨50229697788423456892070645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133945860769129218378855053 50229697788423456892070645)
            ·
              refine ⟨4709034167664699083631623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50229697788423456892070645 4709034167664699083631623)
              ·
                refine ⟨7063551251497048625447435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4709034167664699083631623 7063551251497048625447435)
                ·
                  refine ⟨10595326877245572938171153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7063551251497048625447435 10595326877245572938171153)
                  ·
                    refine ⟨7946495157934179703628365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10595326877245572938171153 7946495157934179703628365)
                    ·
                      refine ⟨2979935684225317388860637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7946495157934179703628365 2979935684225317388860637)
                      ·
                        rfl

theorem cell23_5803404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 1, 1, 2, 3].length) (baseStart_5803404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5803404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5803404 prefixEnd_5803404 := by exact prefixLift 5803404
  have htrace : WordTrace (prefixWord ++ tailWord_5803404) baseStart_5803404 baseEnd_5803404 := by
    simpa [prefixWord, tailWord_5803404, baseEnd_5803404] using wordTrace_append hprefix tailTrace_5803404
  have hstable : (prefixWord ++ tailWord_5803404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5803404).length < 2 ^ (prefixWord ++ tailWord_5803404).sum := by decide
  have hdescent : baseEnd_5803404 < baseStart_5803404 := by decide
  rcases family_descends (prefixWord ++ tailWord_5803404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5803427 : List Nat := [1, 1, 1, 4, 1, 3, 1, 1, 5, 3, 2]
def baseStart_5803427 : Nat := 118140960795 + 5803427 * 2 ^ 59
def prefixEnd_5803427 : Nat := 4983230072969 + 3 ^ 40 * 5803427 * 2
def baseEnd_5803427 : Nat := 2979947494280370798873031

theorem tailTrace_5803427 : CollatzResearch.WordTrace tailWord_5803427 prefixEnd_5803427 2979947494280370798873031 := by
  unfold tailWord_5803427
  simp only [CollatzResearch.WordTrace]
  refine ⟨211668371946182600267512535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141112247964121733511675023 211668371946182600267512535)
  ·
    refine ⟨317502557919273900401268803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211668371946182600267512535 317502557919273900401268803)
    ·
      refine ⟨476253836878910850601903205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317502557919273900401268803 476253836878910850601903205)
      ·
        refine ⟨89297594414795784487856851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 476253836878910850601903205 89297594414795784487856851)
        ·
          refine ⟨133946391622193676731785277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89297594414795784487856851 133946391622193676731785277)
          ·
            refine ⟨50229896858322628774419479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133946391622193676731785277 50229896858322628774419479)
            ·
              refine ⟨75344845287483943161629219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50229896858322628774419479 75344845287483943161629219)
              ·
                refine ⟨113017267931225914742443829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75344845287483943161629219 113017267931225914742443829)
                ·
                  refine ⟨10595368868552429507104109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 113017267931225914742443829 10595368868552429507104109)
                  ·
                    refine ⟨3973263325707161065164041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10595368868552429507104109 3973263325707161065164041)
                    ·
                      refine ⟨2979947494280370798873031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3973263325707161065164041 2979947494280370798873031)
                      ·
                        rfl

theorem cell23_5803427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 5, 3, 2].length) (baseStart_5803427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5803427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5803427 prefixEnd_5803427 := by exact prefixLift 5803427
  have htrace : WordTrace (prefixWord ++ tailWord_5803427) baseStart_5803427 baseEnd_5803427 := by
    simpa [prefixWord, tailWord_5803427, baseEnd_5803427] using wordTrace_append hprefix tailTrace_5803427
  have hstable : (prefixWord ++ tailWord_5803427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5803427).length < 2 ^ (prefixWord ++ tailWord_5803427).sum := by decide
  have hdescent : baseEnd_5803427 < baseStart_5803427 := by decide
  rcases family_descends (prefixWord ++ tailWord_5803427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5803480 : List Nat := [2, 1, 2, 2, 2, 1, 3, 3, 7]
def baseStart_5803480 : Nat := 118140960795 + 5803480 * 2 ^ 59
def prefixEnd_5803480 : Nat := 4983230072969 + 3 ^ 40 * 5803480 * 2
def baseEnd_5803480 : Nat := 331108300972784343501143

theorem tailTrace_5803480 : CollatzResearch.WordTrace tailWord_5803480 prefixEnd_5803480 331108300972784343501143 := by
  unfold tailWord_5803480
  simp only [CollatzResearch.WordTrace]
  refine ⟨105835152507495295159595947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141113536676660393546127929 105835152507495295159595947)
  ·
    refine ⟨158752728761242942739393921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105835152507495295159595947 158752728761242942739393921)
    ·
      refine ⟨119064546570932207054545441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158752728761242942739393921 119064546570932207054545441)
      ·
        refine ⟨89298409928199155290909081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119064546570932207054545441 89298409928199155290909081)
        ·
          refine ⟨66973807446149366468181811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89298409928199155290909081 66973807446149366468181811)
          ·
            refine ⟨100460711169224049702272717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66973807446149366468181811 100460711169224049702272717)
            ·
              refine ⟨37672766688459018638352269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100460711169224049702272717 37672766688459018638352269)
              ·
                refine ⟨14127287508172131989382101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37672766688459018638352269 14127287508172131989382101)
                ·
                  refine ⟨331108300972784343501143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14127287508172131989382101 331108300972784343501143)
                  ·
                    rfl

theorem cell23_5803480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 7].length) (baseStart_5803480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5803480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5803480 prefixEnd_5803480 := by exact prefixLift 5803480
  have htrace : WordTrace (prefixWord ++ tailWord_5803480) baseStart_5803480 baseEnd_5803480 := by
    simpa [prefixWord, tailWord_5803480, baseEnd_5803480] using wordTrace_append hprefix tailTrace_5803480
  have hstable : (prefixWord ++ tailWord_5803480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5803480).length < 2 ^ (prefixWord ++ tailWord_5803480).sum := by decide
  have hdescent : baseEnd_5803480 < baseStart_5803480 := by decide
  rcases family_descends (prefixWord ++ tailWord_5803480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5803491 : List Nat := [1, 1, 1, 6, 2, 3, 1, 1, 1, 4, 2]
def baseStart_5803491 : Nat := 118140960795 + 5803491 * 2 ^ 59
def prefixEnd_5803491 : Nat := 4983230072969 + 3 ^ 40 * 5803491 * 2
def baseEnd_5803491 : Nat := 2979980357042258548472737

theorem tailTrace_5803491 : CollatzResearch.WordTrace tailWord_5803491 prefixEnd_5803491 2979980357042258548472737 := by
  unfold tailWord_5803491
  simp only [CollatzResearch.WordTrace]
  refine ⟨211670706217950739197842327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141113804145300492798561551 211670706217950739197842327)
  ·
    refine ⟨317506059326926108796763491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211670706217950739197842327 317506059326926108796763491)
    ·
      refine ⟨476259088990389163195145237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317506059326926108796763491 476259088990389163195145237)
      ·
        refine ⟨22324644796424492024772433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 476259088990389163195145237 22324644796424492024772433)
        ·
          refine ⟨16743483597318369018579325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22324644796424492024772433 16743483597318369018579325)
          ·
            refine ⟨6278806348994388381967247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16743483597318369018579325 6278806348994388381967247)
            ·
              refine ⟨9418209523491582572950871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6278806348994388381967247 9418209523491582572950871)
              ·
                refine ⟨14127314285237373859426307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9418209523491582572950871 14127314285237373859426307)
                ·
                  refine ⟨21190971427856060789139461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14127314285237373859426307 21190971427856060789139461)
                  ·
                    refine ⟨3973307142723011397963649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21190971427856060789139461 3973307142723011397963649)
                    ·
                      refine ⟨2979980357042258548472737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3973307142723011397963649 2979980357042258548472737)
                      ·
                        rfl

theorem cell23_5803491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_5803491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5803491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5803491 prefixEnd_5803491 := by exact prefixLift 5803491
  have htrace : WordTrace (prefixWord ++ tailWord_5803491) baseStart_5803491 baseEnd_5803491 := by
    simpa [prefixWord, tailWord_5803491, baseEnd_5803491] using wordTrace_append hprefix tailTrace_5803491
  have hstable : (prefixWord ++ tailWord_5803491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5803491).length < 2 ^ (prefixWord ++ tailWord_5803491).sum := by decide
  have hdescent : baseEnd_5803491 < baseStart_5803491 := by decide
  rcases family_descends (prefixWord ++ tailWord_5803491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5803527 : List Nat := [1, 1, 4, 3, 2, 1, 1, 1, 4, 5]
def baseStart_5803527 : Nat := 118140960795 + 5803527 * 2 ^ 59
def prefixEnd_5803527 : Nat := 4983230072969 + 3 ^ 40 * 5803527 * 2
def baseEnd_5803527 : Nat := 993332947448606802540857

theorem tailTrace_5803527 : CollatzResearch.WordTrace tailWord_5803527 prefixEnd_5803527 993332947448606802540857 := by
  unfold tailWord_5803527
  simp only [CollatzResearch.WordTrace]
  refine ⟨211672019245820317346152835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141114679497213544897435223 211672019245820317346152835)
  ·
    refine ⟨317508028868730476019229253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211672019245820317346152835 317508028868730476019229253)
    ·
      refine ⟨59532755412886964253605485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 317508028868730476019229253 59532755412886964253605485)
      ·
        refine ⟨22324783279832611595102057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59532755412886964253605485 22324783279832611595102057)
        ·
          refine ⟨16743587459874458696326543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22324783279832611595102057 16743587459874458696326543)
          ·
            refine ⟨25115381189811688044489815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16743587459874458696326543 25115381189811688044489815)
            ·
              refine ⟨37673071784717532066734723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25115381189811688044489815 37673071784717532066734723)
              ·
                refine ⟨56509607677076298100102085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37673071784717532066734723 56509607677076298100102085)
                ·
                  refine ⟨10595551439451805893769141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56509607677076298100102085 10595551439451805893769141)
                  ·
                    refine ⟨993332947448606802540857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10595551439451805893769141 993332947448606802540857)
                    ·
                      rfl

theorem cell23_5803527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 4, 5].length) (baseStart_5803527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5803527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5803527 prefixEnd_5803527 := by exact prefixLift 5803527
  have htrace : WordTrace (prefixWord ++ tailWord_5803527) baseStart_5803527 baseEnd_5803527 := by
    simpa [prefixWord, tailWord_5803527, baseEnd_5803527] using wordTrace_append hprefix tailTrace_5803527
  have hstable : (prefixWord ++ tailWord_5803527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5803527).length < 2 ^ (prefixWord ++ tailWord_5803527).sum := by decide
  have hdescent : baseEnd_5803527 < baseStart_5803527 := by decide
  rcases family_descends (prefixWord ++ tailWord_5803527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5803531 : List Nat := [1, 1, 1, 1, 8, 1, 3, 2, 5]
def baseStart_5803531 : Nat := 118140960795 + 5803531 * 2 ^ 59
def prefixEnd_5803531 : Nat := 4983230072969 + 3 ^ 40 * 5803531 * 2
def baseEnd_5803531 : Nat := 331111210696493154663617

theorem tailTrace_5803531 : CollatzResearch.WordTrace tailWord_5803531 prefixEnd_5803531 331111210696493154663617 := by
  unfold tailWord_5803531
  simp only [CollatzResearch.WordTrace]
  refine ⟨211672165137805826029298447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141114776758537217352865631 211672165137805826029298447)
  ·
    refine ⟨317508247706708739043947671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211672165137805826029298447 317508247706708739043947671)
    ·
      refine ⟨476262371560063108565921507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317508247706708739043947671 476262371560063108565921507)
      ·
        refine ⟨714393557340094662848882261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 476262371560063108565921507 714393557340094662848882261)
        ·
          refine ⟨8371799500079234330260339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 714393557340094662848882261 8371799500079234330260339)
          ·
            refine ⟨12557699250118851495390509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8371799500079234330260339 12557699250118851495390509)
            ·
              refine ⟨4709137218794569310771441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12557699250118851495390509 4709137218794569310771441)
              ·
                refine ⟨3531852914095926983078581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4709137218794569310771441 3531852914095926983078581)
                ·
                  refine ⟨331111210696493154663617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3531852914095926983078581 331111210696493154663617)
                  ·
                    rfl

theorem cell23_5803531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 2, 5].length) (baseStart_5803531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5803531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5803531 prefixEnd_5803531 := by exact prefixLift 5803531
  have htrace : WordTrace (prefixWord ++ tailWord_5803531) baseStart_5803531 baseEnd_5803531 := by
    simpa [prefixWord, tailWord_5803531, baseEnd_5803531] using wordTrace_append hprefix tailTrace_5803531
  have hstable : (prefixWord ++ tailWord_5803531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5803531).length < 2 ^ (prefixWord ++ tailWord_5803531).sum := by decide
  have hdescent : baseEnd_5803531 < baseStart_5803531 := by decide
  rcases family_descends (prefixWord ++ tailWord_5803531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5803557 : List Nat := [1, 3, 1, 2, 2, 1, 1, 3, 5, 4]
def baseStart_5803557 : Nat := 118140960795 + 5803557 * 2 ^ 59
def prefixEnd_5803557 : Nat := 4983230072969 + 3 ^ 40 * 5803557 * 2
def baseEnd_5803557 : Nat := 993338082255151763415811

theorem tailTrace_5803557 : CollatzResearch.WordTrace tailWord_5803557 prefixEnd_5803557 993338082255151763415811 := by
  unfold tailWord_5803557
  simp only [CollatzResearch.WordTrace]
  refine ⟨211673113435711632469744925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141115408957141088313163283 211673113435711632469744925)
  ·
    refine ⟨79377417538391862176154347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211673113435711632469744925 79377417538391862176154347)
    ·
      refine ⟨119066126307587793264231521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79377417538391862176154347 119066126307587793264231521)
      ·
        refine ⟨89299594730690844948173641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119066126307587793264231521 89299594730690844948173641)
        ·
          refine ⟨66974696048018133711130231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89299594730690844948173641 66974696048018133711130231)
          ·
            refine ⟨100462044072027200566695347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66974696048018133711130231 100462044072027200566695347)
            ·
              refine ⟨150693066108040800850043021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100462044072027200566695347 150693066108040800850043021)
              ·
                refine ⟨56509899790515300318766133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150693066108040800850043021 56509899790515300318766133)
                ·
                  refine ⟨5297803105360809404884325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56509899790515300318766133 5297803105360809404884325)
                  ·
                    refine ⟨993338082255151763415811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5297803105360809404884325 993338082255151763415811)
                    ·
                      rfl

theorem cell23_5803557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 5, 4].length) (baseStart_5803557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5803557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5803557 prefixEnd_5803557 := by exact prefixLift 5803557
  have htrace : WordTrace (prefixWord ++ tailWord_5803557) baseStart_5803557 baseEnd_5803557 := by
    simpa [prefixWord, tailWord_5803557, baseEnd_5803557] using wordTrace_append hprefix tailTrace_5803557
  have hstable : (prefixWord ++ tailWord_5803557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5803557).length < 2 ^ (prefixWord ++ tailWord_5803557).sum := by decide
  have hdescent : baseEnd_5803557 < baseStart_5803557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5803557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5803617 : List Nat := [1, 2, 3, 1, 1, 3, 1, 3, 3, 5]
def baseStart_5803617 : Nat := 118140960795 + 5803617 * 2 ^ 59
def prefixEnd_5803617 : Nat := 4983230072969 + 3 ^ 40 * 5803617 * 2
def baseEnd_5803617 : Nat := 993348351868241685165719

theorem tailTrace_5803617 : CollatzResearch.WordTrace tailWord_5803617 prefixEnd_5803617 993348351868241685165719 := by
  unfold tailWord_5803617
  simp only [CollatzResearch.WordTrace]
  refine ⟨211675301815494262716929105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141116867876996175144619403 211675301815494262716929105)
  ·
    refine ⟨158756476361620697037696829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211675301815494262716929105 158756476361620697037696829)
    ·
      refine ⟨59533678635607761389136311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158756476361620697037696829 59533678635607761389136311)
      ·
        refine ⟨89300517953411642083704467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59533678635607761389136311 89300517953411642083704467)
        ·
          refine ⟨133950776930117463125556701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89300517953411642083704467 133950776930117463125556701)
          ·
            refine ⟨50231541348794048672083763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133950776930117463125556701 50231541348794048672083763)
            ·
              refine ⟨75347312023191073008125645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50231541348794048672083763 75347312023191073008125645)
              ·
                refine ⟨28255242008696652378047117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75347312023191073008125645 28255242008696652378047117)
                ·
                  refine ⟨10595715753261244641767669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28255242008696652378047117 10595715753261244641767669)
                  ·
                    refine ⟨993348351868241685165719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10595715753261244641767669 993348351868241685165719)
                    ·
                      rfl

theorem cell23_5803617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 3, 5].length) (baseStart_5803617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5803617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5803617 prefixEnd_5803617 := by exact prefixLift 5803617
  have htrace : WordTrace (prefixWord ++ tailWord_5803617) baseStart_5803617 baseEnd_5803617 := by
    simpa [prefixWord, tailWord_5803617, baseEnd_5803617] using wordTrace_append hprefix tailTrace_5803617
  have hstable : (prefixWord ++ tailWord_5803617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5803617).length < 2 ^ (prefixWord ++ tailWord_5803617).sum := by decide
  have hdescent : baseEnd_5803617 < baseStart_5803617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5803617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5803657 : List Nat := [1, 2, 1, 1, 4, 1, 3, 1, 3, 1, 5]
def baseStart_5803657 : Nat := 118140960795 + 5803657 * 2 ^ 59
def prefixEnd_5803657 : Nat := 4983230072969 + 3 ^ 40 * 5803657 * 2
def baseEnd_5803657 : Nat := 2980065594830904898996973

theorem tailTrace_5803657 : CollatzResearch.WordTrace tailWord_5803657 prefixEnd_5803657 2980065594830904898996973 := by
  unfold tailWord_5803657
  simp only [CollatzResearch.WordTrace]
  refine ⟨211676760735349349548385225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141117840490232899698923483 211676760735349349548385225)
  ·
    refine ⟨158757570551512012161288919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211676760735349349548385225 158757570551512012161288919)
    ·
      refine ⟨238136355827268018241933379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158757570551512012161288919 238136355827268018241933379)
      ·
        refine ⟨357204533740902027362900069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238136355827268018241933379 357204533740902027362900069)
        ·
          refine ⟨66975850076419130130543763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 357204533740902027362900069 66975850076419130130543763)
          ·
            refine ⟨100463775114628695195815645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66975850076419130130543763 100463775114628695195815645)
            ·
              refine ⟨37673915667985760698430867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100463775114628695195815645 37673915667985760698430867)
              ·
                refine ⟨56510873501978641047646301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37673915667985760698430867 56510873501978641047646301)
                ·
                  refine ⟨21191577563241990392867363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56510873501978641047646301 21191577563241990392867363)
                  ·
                    refine ⟨31787366344862985589301045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21191577563241990392867363 31787366344862985589301045)
                    ·
                      refine ⟨2980065594830904898996973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31787366344862985589301045 2980065594830904898996973)
                      ·
                        rfl

theorem cell23_5803657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 1, 5].length) (baseStart_5803657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5803657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5803657 prefixEnd_5803657 := by exact prefixLift 5803657
  have htrace : WordTrace (prefixWord ++ tailWord_5803657) baseStart_5803657 baseEnd_5803657 := by
    simpa [prefixWord, tailWord_5803657, baseEnd_5803657] using wordTrace_append hprefix tailTrace_5803657
  have hstable : (prefixWord ++ tailWord_5803657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5803657).length < 2 ^ (prefixWord ++ tailWord_5803657).sum := by decide
  have hdescent : baseEnd_5803657 < baseStart_5803657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5803657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5803664 : List Nat := [2, 1, 1, 1, 1, 1, 3, 7, 2, 4]
def baseStart_5803664 : Nat := 118140960795 + 5803664 * 2 ^ 59
def prefixEnd_5803664 : Nat := 4983230072969 + 3 ^ 40 * 5803664 * 2
def baseEnd_5803664 : Nat := 993356396398495457203147

theorem tailTrace_5803664 : CollatzResearch.WordTrace tailWord_5803664 prefixEnd_5803664 993356396398495457203147 := by
  unfold tailWord_5803664
  simp only [CollatzResearch.WordTrace]
  refine ⟨105838508023161994871945023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141118010697549326495926697 105838508023161994871945023)
  ·
    refine ⟨158757762034742992307917535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105838508023161994871945023 158757762034742992307917535)
    ·
      refine ⟨238136643052114488461876303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158757762034742992307917535 238136643052114488461876303)
      ·
        refine ⟨357204964578171732692814455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238136643052114488461876303 357204964578171732692814455)
        ·
          refine ⟨535807446867257599039221683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357204964578171732692814455 535807446867257599039221683)
          ·
            refine ⟨803711170300886398558832525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 535807446867257599039221683 803711170300886398558832525)
            ·
              refine ⟨301391688862832399459562197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 803711170300886398558832525 301391688862832399459562197)
              ·
                refine ⟨7063867707722634362333489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 301391688862832399459562197 7063867707722634362333489)
                ·
                  refine ⟨5297900780791975771750117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7063867707722634362333489 5297900780791975771750117)
                  ·
                    refine ⟨993356396398495457203147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5297900780791975771750117 993356396398495457203147)
                    ·
                      rfl

theorem cell23_5803664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 7, 2, 4].length) (baseStart_5803664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5803664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5803664 prefixEnd_5803664 := by exact prefixLift 5803664
  have htrace : WordTrace (prefixWord ++ tailWord_5803664) baseStart_5803664 baseEnd_5803664 := by
    simpa [prefixWord, tailWord_5803664, baseEnd_5803664] using wordTrace_append hprefix tailTrace_5803664
  have hstable : (prefixWord ++ tailWord_5803664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5803664).length < 2 ^ (prefixWord ++ tailWord_5803664).sum := by decide
  have hdescent : baseEnd_5803664 < baseStart_5803664 := by decide
  rcases family_descends (prefixWord ++ tailWord_5803664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5803668 : List Nat := [2, 4, 2, 2, 2, 1, 2, 2, 1, 5]
def baseStart_5803668 : Nat := 118140960795 + 5803668 * 2 ^ 59
def prefixEnd_5803668 : Nat := 4983230072969 + 3 ^ 40 * 5803668 * 2
def baseEnd_5803668 : Nat := 993357081039368118653141

theorem tailTrace_5803668 : CollatzResearch.WordTrace tailWord_5803668 prefixEnd_5803668 993357081039368118653141 := by
  unfold tailWord_5803668
  simp only [CollatzResearch.WordTrace]
  refine ⟨105838580969154749213517829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141118107958872998951357105 105838580969154749213517829)
  ·
    refine ⟨19844733931716515477534593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105838580969154749213517829 19844733931716515477534593)
    ·
      refine ⟨14883550448787386608150945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19844733931716515477534593 14883550448787386608150945)
      ·
        refine ⟨11162662836590539956113209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14883550448787386608150945 11162662836590539956113209)
        ·
          refine ⟨8371997127442904967084907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11162662836590539956113209 8371997127442904967084907)
          ·
            refine ⟨12557995691164357450627361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8371997127442904967084907 12557995691164357450627361)
            ·
              refine ⟨9418496768373268087970521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12557995691164357450627361 9418496768373268087970521)
              ·
                refine ⟨7063872576279951065977891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9418496768373268087970521 7063872576279951065977891)
                ·
                  refine ⟨10595808864419926598966837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7063872576279951065977891 10595808864419926598966837)
                  ·
                    refine ⟨993357081039368118653141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10595808864419926598966837 993357081039368118653141)
                    ·
                      rfl

theorem cell23_5803668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_5803668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5803668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5803668 prefixEnd_5803668 := by exact prefixLift 5803668
  have htrace : WordTrace (prefixWord ++ tailWord_5803668) baseStart_5803668 baseEnd_5803668 := by
    simpa [prefixWord, tailWord_5803668, baseEnd_5803668] using wordTrace_append hprefix tailTrace_5803668
  have hstable : (prefixWord ++ tailWord_5803668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5803668).length < 2 ^ (prefixWord ++ tailWord_5803668).sum := by decide
  have hdescent : baseEnd_5803668 < baseStart_5803668 := by decide
  rcases family_descends (prefixWord ++ tailWord_5803668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5803671 : List Nat := [1, 1, 3, 3, 2, 3, 2, 2, 1, 1, 4]
def baseStart_5803671 : Nat := 118140960795 + 5803671 * 2 ^ 59
def prefixEnd_5803671 : Nat := 4983230072969 + 3 ^ 40 * 5803671 * 2
def baseEnd_5803671 : Nat := 2980072783560067844221909

theorem tailTrace_5803671 : CollatzResearch.WordTrace tailWord_5803671 prefixEnd_5803671 2980072783560067844221909 := by
  unfold tailWord_5803671
  simp only [CollatzResearch.WordTrace]
  refine ⟨211677271357298629939394867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141118180904865753292929911 211677271357298629939394867)
  ·
    refine ⟨317515907035947944909092301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211677271357298629939394867 317515907035947944909092301)
    ·
      refine ⟨119068465138480479340909613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 317515907035947944909092301 119068465138480479340909613)
      ·
        refine ⟨44650674426930179752841105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119068465138480479340909613 44650674426930179752841105)
        ·
          refine ⟨33488005820197634814630829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44650674426930179752841105 33488005820197634814630829)
          ·
            refine ⟨12558002182574113055486561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33488005820197634814630829 12558002182574113055486561)
            ·
              refine ⟨9418501636930584791614921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12558002182574113055486561 9418501636930584791614921)
              ·
                refine ⟨7063876227697938593711191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9418501636930584791614921 7063876227697938593711191)
                ·
                  refine ⟨10595814341546907890566787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7063876227697938593711191 10595814341546907890566787)
                  ·
                    refine ⟨15893721512320361835850181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10595814341546907890566787 15893721512320361835850181)
                    ·
                      refine ⟨2980072783560067844221909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15893721512320361835850181 2980072783560067844221909)
                      ·
                        rfl

theorem cell23_5803671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_5803671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5803671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5803671 prefixEnd_5803671 := by exact prefixLift 5803671
  have htrace : WordTrace (prefixWord ++ tailWord_5803671) baseStart_5803671 baseEnd_5803671 := by
    simpa [prefixWord, tailWord_5803671, baseEnd_5803671] using wordTrace_append hprefix tailTrace_5803671
  have hstable : (prefixWord ++ tailWord_5803671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5803671).length < 2 ^ (prefixWord ++ tailWord_5803671).sum := by decide
  have hdescent : baseEnd_5803671 < baseStart_5803671 := by decide
  rcases family_descends (prefixWord ++ tailWord_5803671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5803717 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 4, 2, 5]
def baseStart_5803717 : Nat := 118140960795 + 5803717 * 2 ^ 59
def prefixEnd_5803717 : Nat := 4983230072969 + 3 ^ 40 * 5803717 * 2
def baseEnd_5803717 : Nat := 2980096403670174664246697

theorem tailTrace_5803717 : CollatzResearch.WordTrace tailWord_5803717 prefixEnd_5803717 2980096403670174664246697 := by
  unfold tailWord_5803717
  simp only [CollatzResearch.WordTrace]
  refine ⟨211678949115131979795569405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141119299410087986530379603 211678949115131979795569405)
  ·
    refine ⟨79379605918174492423338527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211678949115131979795569405 79379605918174492423338527)
    ·
      refine ⟨119069408877261738635007791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79379605918174492423338527 119069408877261738635007791)
      ·
        refine ⟨178604113315892607952511687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119069408877261738635007791 178604113315892607952511687)
        ·
          refine ⟨267906169973838911928767531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178604113315892607952511687 267906169973838911928767531)
          ·
            refine ⟨401859254960758367893151297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267906169973838911928767531 401859254960758367893151297)
            ·
              refine ⟨301394441220568775919863473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 401859254960758367893151297 301394441220568775919863473)
              ·
                refine ⟨226045830915426581939897605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 301394441220568775919863473 226045830915426581939897605)
                ·
                  refine ⟨42383593296642484113730801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 226045830915426581939897605 42383593296642484113730801)
                  ·
                    refine ⟨31787694972481863085298101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42383593296642484113730801 31787694972481863085298101)
                    ·
                      refine ⟨2980096403670174664246697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31787694972481863085298101 2980096403670174664246697)
                      ·
                        rfl

theorem cell23_5803717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 2, 5].length) (baseStart_5803717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5803717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5803717 prefixEnd_5803717 := by exact prefixLift 5803717
  have htrace : WordTrace (prefixWord ++ tailWord_5803717) baseStart_5803717 baseEnd_5803717 := by
    simpa [prefixWord, tailWord_5803717, baseEnd_5803717] using wordTrace_append hprefix tailTrace_5803717
  have hstable : (prefixWord ++ tailWord_5803717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5803717).length < 2 ^ (prefixWord ++ tailWord_5803717).sum := by decide
  have hdescent : baseEnd_5803717 < baseStart_5803717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5803717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5803718 : List Nat := [6, 1, 2, 1, 1, 1, 2, 1, 1, 1, 6]
def baseStart_5803718 : Nat := 118140960795 + 5803718 * 2 ^ 59
def prefixEnd_5803718 : Nat := 4983230072969 + 3 ^ 40 * 5803718 * 2
def baseEnd_5803718 : Nat := 2980096917150829160334193

theorem tailTrace_5803718 : CollatzResearch.WordTrace tailWord_5803718 prefixEnd_5803718 2980096917150829160334193 := by
  unfold tailWord_5803718
  simp only [CollatzResearch.WordTrace]
  refine ⟨6614968299629011155198619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 141119323725418904644237205 6614968299629011155198619)
  ·
    refine ⟨9922452449443516732797929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6614968299629011155198619 9922452449443516732797929)
    ·
      refine ⟨7441839337082637549598447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9922452449443516732797929 7441839337082637549598447)
      ·
        refine ⟨11162759005623956324397671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7441839337082637549598447 11162759005623956324397671)
        ·
          refine ⟨16744138508435934486596507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11162759005623956324397671 16744138508435934486596507)
          ·
            refine ⟨25116207762653901729894761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16744138508435934486596507 25116207762653901729894761)
            ·
              refine ⟨18837155821990426297421071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25116207762653901729894761 18837155821990426297421071)
              ·
                refine ⟨28255733732985639446131607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18837155821990426297421071 28255733732985639446131607)
                ·
                  refine ⟨42383600599478459169197411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28255733732985639446131607 42383600599478459169197411)
                  ·
                    refine ⟨63575400899217688753796117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42383600599478459169197411 63575400899217688753796117)
                    ·
                      refine ⟨2980096917150829160334193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63575400899217688753796117 2980096917150829160334193)
                      ·
                        rfl

theorem cell23_5803718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_5803718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5803718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5803718 prefixEnd_5803718 := by exact prefixLift 5803718
  have htrace : WordTrace (prefixWord ++ tailWord_5803718) baseStart_5803718 baseEnd_5803718 := by
    simpa [prefixWord, tailWord_5803718, baseEnd_5803718] using wordTrace_append hprefix tailTrace_5803718
  have hstable : (prefixWord ++ tailWord_5803718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5803718).length < 2 ^ (prefixWord ++ tailWord_5803718).sum := by decide
  have hdescent : baseEnd_5803718 < baseStart_5803718 := by decide
  rcases family_descends (prefixWord ++ tailWord_5803718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5803725 : List Nat := [1, 6, 2, 1, 1, 1, 3, 2, 1, 2, 3]
def baseStart_5803725 : Nat := 118140960795 + 5803725 * 2 ^ 59
def prefixEnd_5803725 : Nat := 4983230072969 + 3 ^ 40 * 5803725 * 2
def baseEnd_5803725 : Nat := 2980100511515410632946661

theorem tailTrace_5803725 : CollatzResearch.WordTrace tailWord_5803725 prefixEnd_5803725 2980100511515410632946661 := by
  unfold tailWord_5803725
  simp only [CollatzResearch.WordTrace]
  refine ⟨211679240899102997161860629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141119493932735331441240419 211679240899102997161860629)
  ·
    refine ⟨9922464417145452991962217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 211679240899102997161860629 9922464417145452991962217)
    ·
      refine ⟨7441848312859089743971663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9922464417145452991962217 7441848312859089743971663)
      ·
        refine ⟨11162772469288634615957495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7441848312859089743971663 11162772469288634615957495)
        ·
          refine ⟨16744158703932951923936243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11162772469288634615957495 16744158703932951923936243)
          ·
            refine ⟨25116238055899427885904365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16744158703932951923936243 25116238055899427885904365)
            ·
              refine ⟨9418589270962285457214137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25116238055899427885904365 9418589270962285457214137)
              ·
                refine ⟨7063941953221714092910603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9418589270962285457214137 7063941953221714092910603)
                ·
                  refine ⟨10595912929832571139365905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7063941953221714092910603 10595912929832571139365905)
                  ·
                    refine ⟨7946934697374428354524429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10595912929832571139365905 7946934697374428354524429)
                    ·
                      refine ⟨2980100511515410632946661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7946934697374428354524429 2980100511515410632946661)
                      ·
                        rfl

theorem cell23_5803725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_5803725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5803725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5803725 prefixEnd_5803725 := by exact prefixLift 5803725
  have htrace : WordTrace (prefixWord ++ tailWord_5803725) baseStart_5803725 baseEnd_5803725 := by
    simpa [prefixWord, tailWord_5803725, baseEnd_5803725] using wordTrace_append hprefix tailTrace_5803725
  have hstable : (prefixWord ++ tailWord_5803725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5803725).length < 2 ^ (prefixWord ++ tailWord_5803725).sum := by decide
  have hdescent : baseEnd_5803725 < baseStart_5803725 := by decide
  rcases family_descends (prefixWord ++ tailWord_5803725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5803784 : List Nat := [2, 1, 3, 2, 2, 1, 3, 2, 7]
def baseStart_5803784 : Nat := 118140960795 + 5803784 * 2 ^ 59
def prefixEnd_5803784 : Nat := 4983230072969 + 3 ^ 40 * 5803784 * 2
def baseEnd_5803784 : Nat := 331125645208225100234321

theorem tailTrace_5803784 : CollatzResearch.WordTrace tailWord_5803784 prefixEnd_5803784 331125645208225100234321 := by
  unfold tailWord_5803784
  simp only [CollatzResearch.WordTrace]
  refine ⟨105840696402944625119129203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141120928537259500158838937 105840696402944625119129203)
  ·
    refine ⟨158761044604416937678693805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105840696402944625119129203 158761044604416937678693805)
    ·
      refine ⟨59535391726656351629510177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158761044604416937678693805 59535391726656351629510177)
      ·
        refine ⟨44651543794992263722132633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59535391726656351629510177 44651543794992263722132633)
        ·
          refine ⟨33488657846244197791599475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44651543794992263722132633 33488657846244197791599475)
          ·
            refine ⟨50232986769366296687399213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33488657846244197791599475 50232986769366296687399213)
            ·
              refine ⟨18837370038512361257774705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50232986769366296687399213 18837370038512361257774705)
              ·
                refine ⟨14128027528884270943331029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18837370038512361257774705 14128027528884270943331029)
                ·
                  refine ⟨331125645208225100234321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14128027528884270943331029 331125645208225100234321)
                  ·
                    rfl

theorem cell23_5803784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 7].length) (baseStart_5803784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5803784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5803784 prefixEnd_5803784 := by exact prefixLift 5803784
  have htrace : WordTrace (prefixWord ++ tailWord_5803784) baseStart_5803784 baseEnd_5803784 := by
    simpa [prefixWord, tailWord_5803784, baseEnd_5803784] using wordTrace_append hprefix tailTrace_5803784
  have hstable : (prefixWord ++ tailWord_5803784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5803784).length < 2 ^ (prefixWord ++ tailWord_5803784).sum := by decide
  have hdescent : baseEnd_5803784 < baseStart_5803784 := by decide
  rcases family_descends (prefixWord ++ tailWord_5803784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5803806 : List Nat := [4, 3, 2, 2, 2, 1, 1, 2, 2, 1, 3]
def baseStart_5803806 : Nat := 118140960795 + 5803806 * 2 ^ 59
def prefixEnd_5803806 : Nat := 4983230072969 + 3 ^ 40 * 5803806 * 2
def baseEnd_5803806 : Nat := 2980142103448424816033789

theorem tailTrace_5803806 : CollatzResearch.WordTrace tailWord_5803806 prefixEnd_5803806 2980142103448424816033789 := by
  unfold tailWord_5803806
  simp only [CollatzResearch.WordTrace]
  refine ⟨26460274401476193499444909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141121463474539698663706181 26460274401476193499444909)
  ·
    refine ⟨9922602900553572562291841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26460274401476193499444909 9922602900553572562291841)
    ·
      refine ⟨7441952175415179421718881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9922602900553572562291841 7441952175415179421718881)
      ·
        refine ⟨5581464131561384566289161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7441952175415179421718881 5581464131561384566289161)
        ·
          refine ⟨4186098098671038424716871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5581464131561384566289161 4186098098671038424716871)
          ·
            refine ⟨6279147148006557637075307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4186098098671038424716871 6279147148006557637075307)
            ·
              refine ⟨9418720722009836455612961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6279147148006557637075307 9418720722009836455612961)
              ·
                refine ⟨7064040541507377341709721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9418720722009836455612961 7064040541507377341709721)
                ·
                  refine ⟨5298030406130533006282291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7064040541507377341709721 5298030406130533006282291)
                  ·
                    refine ⟨7947045609195799509423437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5298030406130533006282291 7947045609195799509423437)
                    ·
                      refine ⟨2980142103448424816033789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7947045609195799509423437 2980142103448424816033789)
                      ·
                        rfl

theorem cell23_5803806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_5803806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5803806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5803806 prefixEnd_5803806 := by exact prefixLift 5803806
  have htrace : WordTrace (prefixWord ++ tailWord_5803806) baseStart_5803806 baseEnd_5803806 := by
    simpa [prefixWord, tailWord_5803806, baseEnd_5803806] using wordTrace_append hprefix tailTrace_5803806
  have hstable : (prefixWord ++ tailWord_5803806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5803806).length < 2 ^ (prefixWord ++ tailWord_5803806).sum := by decide
  have hdescent : baseEnd_5803806 < baseStart_5803806 := by decide
  rcases family_descends (prefixWord ++ tailWord_5803806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5803812 : List Nat := [2, 3, 1, 3, 2, 3, 1, 2, 2, 2, 2]
def baseStart_5803812 : Nat := 118140960795 + 5803812 * 2 ^ 59
def prefixEnd_5803812 : Nat := 4983230072969 + 3 ^ 40 * 5803812 * 2
def baseEnd_5803812 : Nat := 2980145184332351792558761

theorem tailTrace_5803812 : CollatzResearch.WordTrace tailWord_5803812 prefixEnd_5803812 2980145184332351792558761 := by
  unfold tailWord_5803812
  simp only [CollatzResearch.WordTrace]
  refine ⟨105841207024893905510138845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141121609366525207346851793 105841207024893905510138845)
  ·
    refine ⟨39690452634335214566302067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105841207024893905510138845 39690452634335214566302067)
    ·
      refine ⟨59535678951502821849453101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39690452634335214566302067 59535678951502821849453101)
      ·
        refine ⟨22325879606813558193544913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59535678951502821849453101 22325879606813558193544913)
        ·
          refine ⟨16744409705110168645158685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22325879606813558193544913 16744409705110168645158685)
          ·
            refine ⟨6279153639416313241934507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16744409705110168645158685 6279153639416313241934507)
            ·
              refine ⟨9418730459124469862901761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6279153639416313241934507 9418730459124469862901761)
              ·
                refine ⟨7064047844343352397176321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9418730459124469862901761 7064047844343352397176321)
                ·
                  refine ⟨5298035883257514297882241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7064047844343352397176321 5298035883257514297882241)
                  ·
                    refine ⟨3973526912443135723411681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5298035883257514297882241 3973526912443135723411681)
                    ·
                      refine ⟨2980145184332351792558761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3973526912443135723411681 2980145184332351792558761)
                      ·
                        rfl

theorem cell23_5803812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_5803812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5803812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5803812 prefixEnd_5803812 := by exact prefixLift 5803812
  have htrace : WordTrace (prefixWord ++ tailWord_5803812) baseStart_5803812 baseEnd_5803812 := by
    simpa [prefixWord, tailWord_5803812, baseEnd_5803812] using wordTrace_append hprefix tailTrace_5803812
  have hstable : (prefixWord ++ tailWord_5803812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5803812).length < 2 ^ (prefixWord ++ tailWord_5803812).sum := by decide
  have hdescent : baseEnd_5803812 < baseStart_5803812 := by decide
  rcases family_descends (prefixWord ++ tailWord_5803812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5803828 : List Nat := [2, 5, 1, 1, 2, 1, 2, 1, 2, 3, 3]
def baseStart_5803828 : Nat := 118140960795 + 5803828 * 2 ^ 59
def prefixEnd_5803828 : Nat := 4983230072969 + 3 ^ 40 * 5803828 * 2
def baseEnd_5803828 : Nat := 2980153400022823729958687

theorem tailTrace_5803828 : CollatzResearch.WordTrace tailWord_5803828 prefixEnd_5803828 2980153400022823729958687 := by
  unfold tailWord_5803828
  simp only [CollatzResearch.WordTrace]
  refine ⟨105841498808864922876430069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141121998411819897168573425 105841498808864922876430069)
  ·
    refine ⟨9922640513331086519665319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 105841498808864922876430069 9922640513331086519665319)
    ·
      refine ⟨14883960769996629779497979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9922640513331086519665319 14883960769996629779497979)
      ·
        refine ⟨22325941154994944669246969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14883960769996629779497979 22325941154994944669246969)
        ·
          refine ⟨16744455866246208501935227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22325941154994944669246969 16744455866246208501935227)
          ·
            refine ⟨25116683799369312752902841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16744455866246208501935227 25116683799369312752902841)
            ·
              refine ⟨18837512849526984564677131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25116683799369312752902841 18837512849526984564677131)
              ·
                refine ⟨28256269274290476847015697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18837512849526984564677131 28256269274290476847015697)
                ·
                  refine ⟨21192201955717857635261773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28256269274290476847015697 21192201955717857635261773)
                  ·
                    refine ⟨7947075733394196613223165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21192201955717857635261773 7947075733394196613223165)
                    ·
                      refine ⟨2980153400022823729958687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7947075733394196613223165 2980153400022823729958687)
                      ·
                        rfl

theorem cell23_5803828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_5803828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5803828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5803828 prefixEnd_5803828 := by exact prefixLift 5803828
  have htrace : WordTrace (prefixWord ++ tailWord_5803828) baseStart_5803828 baseEnd_5803828 := by
    simpa [prefixWord, tailWord_5803828, baseEnd_5803828] using wordTrace_append hprefix tailTrace_5803828
  have hstable : (prefixWord ++ tailWord_5803828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5803828).length < 2 ^ (prefixWord ++ tailWord_5803828).sum := by decide
  have hdescent : baseEnd_5803828 < baseStart_5803828 := by decide
  rcases family_descends (prefixWord ++ tailWord_5803828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5803854 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 4, 3, 5]
def baseStart_5803854 : Nat := 118140960795 + 5803854 * 2 ^ 59
def prefixEnd_5803854 : Nat := 4983230072969 + 3 ^ 40 * 5803854 * 2
def baseEnd_5803854 : Nat := 2980166750519840628233567

theorem tailTrace_5803854 : CollatzResearch.WordTrace tailWord_5803854 prefixEnd_5803854 2980166750519840628233567 := by
  unfold tailWord_5803854
  simp only [CollatzResearch.WordTrace]
  refine ⟨26460493239454456524163327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141122630610423768128871077 26460493239454456524163327)
  ·
    refine ⟨39690739859181684786244991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26460493239454456524163327 39690739859181684786244991)
    ·
      refine ⟨59536109788772527179367487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39690739859181684786244991 59536109788772527179367487)
      ·
        refine ⟨89304164683158790769051231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59536109788772527179367487 89304164683158790769051231)
        ·
          refine ⟨133956247024738186153576847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89304164683158790769051231 133956247024738186153576847)
          ·
            refine ⟨200934370537107279230365271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133956247024738186153576847 200934370537107279230365271)
            ·
              refine ⟨301401555805660918845547907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200934370537107279230365271 301401555805660918845547907)
              ·
                refine ⟨452102333708491378268321861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 301401555805660918845547907 452102333708491378268321861)
                ·
                  refine ⟨84769187570342133425310349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 452102333708491378268321861 84769187570342133425310349)
                  ·
                    refine ⟨31788445338878300034491381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 84769187570342133425310349 31788445338878300034491381)
                    ·
                      refine ⟨2980166750519840628233567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31788445338878300034491381 2980166750519840628233567)
                      ·
                        rfl

theorem cell23_5803854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_5803854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5803854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5803854 prefixEnd_5803854 := by exact prefixLift 5803854
  have htrace : WordTrace (prefixWord ++ tailWord_5803854) baseStart_5803854 baseEnd_5803854 := by
    simpa [prefixWord, tailWord_5803854, baseEnd_5803854] using wordTrace_append hprefix tailTrace_5803854
  have hstable : (prefixWord ++ tailWord_5803854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5803854).length < 2 ^ (prefixWord ++ tailWord_5803854).sum := by decide
  have hdescent : baseEnd_5803854 < baseStart_5803854 := by decide
  rcases family_descends (prefixWord ++ tailWord_5803854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5803871 : List Nat := [1, 1, 2, 3, 1, 4, 1, 1, 4, 2, 3]
def baseStart_5803871 : Nat := 118140960795 + 5803871 * 2 ^ 59
def prefixEnd_5803871 : Nat := 4983230072969 + 3 ^ 40 * 5803871 * 2
def baseEnd_5803871 : Nat := 2980175479690967061720989

theorem tailTrace_5803871 : CollatzResearch.WordTrace tailWord_5803871 prefixEnd_5803871 2980175479690967061720989 := by
  unfold tailWord_5803871
  simp only [CollatzResearch.WordTrace]
  refine ⟨211684565956574064096675467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141123043971049376064450311 211684565956574064096675467)
  ·
    refine ⟨317526848934861096145013201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211684565956574064096675467 317526848934861096145013201)
    ·
      refine ⟨238145136701145822108759901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317526848934861096145013201 238145136701145822108759901)
      ·
        refine ⟨89304426262929683290784963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238145136701145822108759901 89304426262929683290784963)
        ·
          refine ⟨133956639394394524936177445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89304426262929683290784963 133956639394394524936177445)
          ·
            refine ⟨25116869886448973425533271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 133956639394394524936177445 25116869886448973425533271)
            ·
              refine ⟨37675304829673460138299907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25116869886448973425533271 37675304829673460138299907)
              ·
                refine ⟨56512957244510190207449861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37675304829673460138299907 56512957244510190207449861)
                ·
                  refine ⟨10596179483345660663896849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56512957244510190207449861 10596179483345660663896849)
                  ·
                    refine ⟨7947134612509245497922637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10596179483345660663896849 7947134612509245497922637)
                    ·
                      refine ⟨2980175479690967061720989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7947134612509245497922637 2980175479690967061720989)
                      ·
                        rfl

theorem cell23_5803871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 4, 2, 3].length) (baseStart_5803871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5803871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5803871 prefixEnd_5803871 := by exact prefixLift 5803871
  have htrace : WordTrace (prefixWord ++ tailWord_5803871) baseStart_5803871 baseEnd_5803871 := by
    simpa [prefixWord, tailWord_5803871, baseEnd_5803871] using wordTrace_append hprefix tailTrace_5803871
  have hstable : (prefixWord ++ tailWord_5803871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5803871).length < 2 ^ (prefixWord ++ tailWord_5803871).sum := by decide
  have hdescent : baseEnd_5803871 < baseStart_5803871 := by decide
  rcases family_descends (prefixWord ++ tailWord_5803871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5803921 : List Nat := [1, 2, 2, 1, 1, 1, 4, 5, 1, 5]
def baseStart_5803921 : Nat := 118140960795 + 5803921 * 2 ^ 59
def prefixEnd_5803921 : Nat := 4983230072969 + 3 ^ 40 * 5803921 * 2
def baseEnd_5803921 : Nat := 993400384574563955365253

theorem tailTrace_5803921 : CollatzResearch.WordTrace tailWord_5803921 prefixEnd_5803921 993400384574563955365253 := by
  unfold tailWord_5803921
  simp only [CollatzResearch.WordTrace]
  refine ⟨211686389606392922635995617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141124259737595281757330411 211686389606392922635995617)
  ·
    refine ⟨158764792204794691976996713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211686389606392922635995617 158764792204794691976996713)
    ·
      refine ⟨119073594153596018982747535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158764792204794691976996713 119073594153596018982747535)
      ·
        refine ⟨178610391230394028474121303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119073594153596018982747535 178610391230394028474121303)
        ·
          refine ⟨267915586845591042711181955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178610391230394028474121303 267915586845591042711181955)
          ·
            refine ⟨401873380268386564066772933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267915586845591042711181955 401873380268386564066772933)
            ·
              refine ⟨75351258800322480762519925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 401873380268386564066772933 75351258800322480762519925)
              ·
                refine ⟨7064180512530232571486243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75351258800322480762519925 7064180512530232571486243)
                ·
                  refine ⟨10596270768795348857229365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7064180512530232571486243 10596270768795348857229365)
                  ·
                    refine ⟨993400384574563955365253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10596270768795348857229365 993400384574563955365253)
                    ·
                      rfl

theorem cell23_5803921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 5].length) (baseStart_5803921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5803921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5803921 prefixEnd_5803921 := by exact prefixLift 5803921
  have htrace : WordTrace (prefixWord ++ tailWord_5803921) baseStart_5803921 baseEnd_5803921 := by
    simpa [prefixWord, tailWord_5803921, baseEnd_5803921] using wordTrace_append hprefix tailTrace_5803921
  have hstable : (prefixWord ++ tailWord_5803921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5803921).length < 2 ^ (prefixWord ++ tailWord_5803921).sum := by decide
  have hdescent : baseEnd_5803921 < baseStart_5803921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5803921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5803951 : List Nat := [1, 1, 2, 1, 2, 2, 6, 1, 1, 6]
def baseStart_5803951 : Nat := 118140960795 + 5803951 * 2 ^ 59
def prefixEnd_5803951 : Nat := 4983230072969 + 3 ^ 40 * 5803951 * 2
def baseEnd_5803951 : Nat := 993405519381108916240207

theorem tailTrace_5803951 : CollatzResearch.WordTrace tailWord_5803951 prefixEnd_5803951 993405519381108916240207 := by
  unfold tailWord_5803951
  simp only [CollatzResearch.WordTrace]
  refine ⟨211687483796284237759587707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141124989197522825173058471 211687483796284237759587707)
  ·
    refine ⟨317531225694426356639381561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211687483796284237759587707 317531225694426356639381561)
    ·
      refine ⟨238148419270819767479536171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317531225694426356639381561 238148419270819767479536171)
      ·
        refine ⟨357222628906229651219304257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238148419270819767479536171 357222628906229651219304257)
        ·
          refine ⟨267916971679672238414478193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 357222628906229651219304257 267916971679672238414478193)
          ·
            refine ⟨200937728759754178810858645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267916971679672238414478193 200937728759754178810858645)
            ·
              refine ⟨9418956035613477131758999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 200937728759754178810858645 9418956035613477131758999)
              ·
                refine ⟨14128434053420215697638499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9418956035613477131758999 14128434053420215697638499)
                ·
                  refine ⟨21192651080130323546457749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14128434053420215697638499 21192651080130323546457749)
                  ·
                    refine ⟨993405519381108916240207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21192651080130323546457749 993405519381108916240207)
                    ·
                      rfl

theorem cell23_5803951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 6].length) (baseStart_5803951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5803951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5803951 prefixEnd_5803951 := by exact prefixLift 5803951
  have htrace : WordTrace (prefixWord ++ tailWord_5803951) baseStart_5803951 baseEnd_5803951 := by
    simpa [prefixWord, tailWord_5803951, baseEnd_5803951] using wordTrace_append hprefix tailTrace_5803951
  have hstable : (prefixWord ++ tailWord_5803951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5803951).length < 2 ^ (prefixWord ++ tailWord_5803951).sum := by decide
  have hdescent : baseEnd_5803951 < baseStart_5803951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5803951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5803992 : List Nat := [2, 1, 2, 2, 2, 2, 1, 6, 1, 2, 2]
def baseStart_5803992 : Nat := 118140960795 + 5803992 * 2 ^ 59
def prefixEnd_5803992 : Nat := 4983230072969 + 3 ^ 40 * 5803992 * 2
def baseEnd_5803992 : Nat := 2980237610850161088307933

theorem tailTrace_5803992 : CollatzResearch.WordTrace tailWord_5803992 prefixEnd_5803992 2980237610850161088307933 := by
  unfold tailWord_5803992
  simp only [CollatzResearch.WordTrace]
  refine ⟨105844489594567850880915115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141125986126090467841220153 105844489594567850880915115)
  ·
    refine ⟨158766734391851776321372673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105844489594567850880915115 158766734391851776321372673)
    ·
      refine ⟨119075050793888832241029505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158766734391851776321372673 119075050793888832241029505)
      ·
        refine ⟨89306288095416624180772129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119075050793888832241029505 89306288095416624180772129)
        ·
          refine ⟨66979716071562468135579097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89306288095416624180772129 66979716071562468135579097)
          ·
            refine ⟨50234787053671851101684323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66979716071562468135579097 50234787053671851101684323)
            ·
              refine ⟨75352180580507776652526485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50234787053671851101684323 75352180580507776652526485)
              ·
                refine ⟨3532133464711302030587179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 75352180580507776652526485 3532133464711302030587179)
                ·
                  refine ⟨5298200197066953045880769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3532133464711302030587179 5298200197066953045880769)
                  ·
                    refine ⟨3973650147800214784410577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5298200197066953045880769 3973650147800214784410577)
                    ·
                      refine ⟨2980237610850161088307933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3973650147800214784410577 2980237610850161088307933)
                      ·
                        rfl

theorem cell23_5803992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 6, 1, 2, 2].length) (baseStart_5803992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5803992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5803992 prefixEnd_5803992 := by exact prefixLift 5803992
  have htrace : WordTrace (prefixWord ++ tailWord_5803992) baseStart_5803992 baseEnd_5803992 := by
    simpa [prefixWord, tailWord_5803992, baseEnd_5803992] using wordTrace_append hprefix tailTrace_5803992
  have hstable : (prefixWord ++ tailWord_5803992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5803992).length < 2 ^ (prefixWord ++ tailWord_5803992).sum := by decide
  have hdescent : baseEnd_5803992 < baseStart_5803992 := by decide
  rcases family_descends (prefixWord ++ tailWord_5803992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5804002 : List Nat := [3, 3, 3, 1, 2, 2, 1, 1, 1, 6]
def baseStart_5804002 : Nat := 118140960795 + 5804002 * 2 ^ 59
def prefixEnd_5804002 : Nat := 4983230072969 + 3 ^ 40 * 5804002 * 2
def baseEnd_5804002 : Nat := 993414248552235349727629

theorem tailTrace_5804002 : CollatzResearch.WordTrace tailWord_5804002 prefixEnd_5804002 993414248552235349727629 := by
  unfold tailWord_5804002
  simp only [CollatzResearch.WordTrace]
  refine ⟨52922335979774868367423565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141126229279399648979796173 52922335979774868367423565)
  ·
    refine ⟨19845875992415575637783837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52922335979774868367423565 19845875992415575637783837)
    ·
      refine ⟨7442203497155840864168939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19845875992415575637783837 7442203497155840864168939)
      ·
        refine ⟨11163305245733761296253409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7442203497155840864168939 11163305245733761296253409)
        ·
          refine ⟨8372478934300320972190057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11163305245733761296253409 8372478934300320972190057)
          ·
            refine ⟨6279359200725240729142543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8372478934300320972190057 6279359200725240729142543)
            ·
              refine ⟨9419038801087861093713815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6279359200725240729142543 9419038801087861093713815)
              ·
                refine ⟨14128558201631791640570723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9419038801087861093713815 14128558201631791640570723)
                ·
                  refine ⟨21192837302447687460856085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14128558201631791640570723 21192837302447687460856085)
                  ·
                    refine ⟨993414248552235349727629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21192837302447687460856085 993414248552235349727629)
                    ·
                      rfl

theorem cell23_5804002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_5804002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5804002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5804002 prefixEnd_5804002 := by exact prefixLift 5804002
  have htrace : WordTrace (prefixWord ++ tailWord_5804002) baseStart_5804002 baseEnd_5804002 := by
    simpa [prefixWord, tailWord_5804002, baseEnd_5804002] using wordTrace_append hprefix tailTrace_5804002
  have hstable : (prefixWord ++ tailWord_5804002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5804002).length < 2 ^ (prefixWord ++ tailWord_5804002).sum := by decide
  have hdescent : baseEnd_5804002 < baseStart_5804002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5804002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5804048 : List Nat := [2, 1, 1, 1, 1, 1, 1, 6, 3, 4, 2]
def baseStart_5804048 : Nat := 118140960795 + 5804048 * 2 ^ 59
def prefixEnd_5804048 : Nat := 4983230072969 + 3 ^ 40 * 5804048 * 2
def baseEnd_5804048 : Nat := 2980266365766812869207675

theorem tailTrace_5804048 : CollatzResearch.WordTrace tailWord_5804048 prefixEnd_5804048 2980266365766812869207675 := by
  unfold tailWord_5804048
  simp only [CollatzResearch.WordTrace]
  refine ⟨105845510838466411662934399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141127347784621882217245865 105845510838466411662934399)
  ·
    refine ⟨158768266257699617494401599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105845510838466411662934399 158768266257699617494401599)
    ·
      refine ⟨238152399386549426241602399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158768266257699617494401599 238152399386549426241602399)
      ·
        refine ⟨357228599079824139362403599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238152399386549426241602399 357228599079824139362403599)
        ·
          refine ⟨535842898619736209043605399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357228599079824139362403599 535842898619736209043605399)
          ·
            refine ⟨803764347929604313565408099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 535842898619736209043605399 803764347929604313565408099)
            ·
              refine ⟨1205646521894406470348112149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 803764347929604313565408099 1205646521894406470348112149)
              ·
                refine ⟨56514680713800303297567757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1205646521894406470348112149 56514680713800303297567757)
                ·
                  refine ⟨21193005267675113736587909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56514680713800303297567757 21193005267675113736587909)
                  ·
                    refine ⟨3973688487689083825610233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21193005267675113736587909 3973688487689083825610233)
                    ·
                      refine ⟨2980266365766812869207675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3973688487689083825610233 2980266365766812869207675)
                      ·
                        rfl

theorem cell23_5804048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 3, 4, 2].length) (baseStart_5804048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5804048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5804048 prefixEnd_5804048 := by exact prefixLift 5804048
  have htrace : WordTrace (prefixWord ++ tailWord_5804048) baseStart_5804048 baseEnd_5804048 := by
    simpa [prefixWord, tailWord_5804048, baseEnd_5804048] using wordTrace_append hprefix tailTrace_5804048
  have hstable : (prefixWord ++ tailWord_5804048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5804048).length < 2 ^ (prefixWord ++ tailWord_5804048).sum := by decide
  have hdescent : baseEnd_5804048 < baseStart_5804048 := by decide
  rcases family_descends (prefixWord ++ tailWord_5804048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5804101 : List Nat := [1, 3, 1, 1, 1, 3, 1, 2, 3, 7]
def baseStart_5804101 : Nat := 118140960795 + 5804101 * 2 ^ 59
def prefixEnd_5804101 : Nat := 4983230072969 + 3 ^ 40 * 5804101 * 2
def baseEnd_5804101 : Nat := 993431193413833720614977

theorem tailTrace_5804101 : CollatzResearch.WordTrace tailWord_5804101 prefixEnd_5804101 993431193413833720614977 := by
  unfold tailWord_5804101
  simp only [CollatzResearch.WordTrace]
  refine ⟨211692954745740813377548157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141128636497160542251698771 211692954745740813377548157)
  ·
    refine ⟨79384858029652805016580559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211692954745740813377548157 79384858029652805016580559)
    ·
      refine ⟨119077287044479207524870839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79384858029652805016580559 119077287044479207524870839)
      ·
        refine ⟨178615930566718811287306259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119077287044479207524870839 178615930566718811287306259)
        ·
          refine ⟨267923895850078216930959389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178615930566718811287306259 267923895850078216930959389)
          ·
            refine ⟨100471460943779331349109771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 267923895850078216930959389 100471460943779331349109771)
            ·
              refine ⟨150707191415668997023664657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100471460943779331349109771 150707191415668997023664657)
              ·
                refine ⟨113030393561751747767748493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150707191415668997023664657 113030393561751747767748493)
                ·
                  refine ⟨42386397585656905412905685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113030393561751747767748493 42386397585656905412905685)
                  ·
                    refine ⟨993431193413833720614977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42386397585656905412905685 993431193413833720614977)
                    ·
                      rfl

theorem cell23_5804101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 7].length) (baseStart_5804101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5804101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5804101 prefixEnd_5804101 := by exact prefixLift 5804101
  have htrace : WordTrace (prefixWord ++ tailWord_5804101) baseStart_5804101 baseEnd_5804101 := by
    simpa [prefixWord, tailWord_5804101, baseEnd_5804101] using wordTrace_append hprefix tailTrace_5804101
  have hstable : (prefixWord ++ tailWord_5804101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5804101).length < 2 ^ (prefixWord ++ tailWord_5804101).sum := by decide
  have hdescent : baseEnd_5804101 < baseStart_5804101 := by decide
  rcases family_descends (prefixWord ++ tailWord_5804101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5804165 : List Nat := [1, 3, 1, 1, 5, 1, 1, 3, 3, 4]
def baseStart_5804165 : Nat := 118140960795 + 5804165 * 2 ^ 59
def prefixEnd_5804165 : Nat := 4983230072969 + 3 ^ 40 * 5804165 * 2
def baseEnd_5804165 : Nat := 993442147667796303814879

theorem tailTrace_5804165 : CollatzResearch.WordTrace tailWord_5804165 prefixEnd_5804165 993442147667796303814879 := by
  unfold tailWord_5804165
  simp only [CollatzResearch.WordTrace]
  refine ⟨211695289017508952307877949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141130192678339301538585299 211695289017508952307877949)
  ·
    refine ⟨79385733381565857115454231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211695289017508952307877949 79385733381565857115454231)
    ·
      refine ⟨119078600072348785673181347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79385733381565857115454231 119078600072348785673181347)
      ·
        refine ⟨178617900108523178509772021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119078600072348785673181347 178617900108523178509772021)
        ·
          refine ⟨16745428135174047985291127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 178617900108523178509772021 16745428135174047985291127)
          ·
            refine ⟨25118142202761071977936691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16745428135174047985291127 25118142202761071977936691)
            ·
              refine ⟨37677213304141607966905037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25118142202761071977936691 37677213304141607966905037)
              ·
                refine ⟨14128954989053102987589389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37677213304141607966905037 14128954989053102987589389)
                ·
                  refine ⟨5298358120894913620346021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14128954989053102987589389 5298358120894913620346021)
                  ·
                    refine ⟨993442147667796303814879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5298358120894913620346021 993442147667796303814879)
                    ·
                      rfl

theorem cell23_5804165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 3, 4].length) (baseStart_5804165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5804165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5804165 prefixEnd_5804165 := by exact prefixLift 5804165
  have htrace : WordTrace (prefixWord ++ tailWord_5804165) baseStart_5804165 baseEnd_5804165 := by
    simpa [prefixWord, tailWord_5804165, baseEnd_5804165] using wordTrace_append hprefix tailTrace_5804165
  have hstable : (prefixWord ++ tailWord_5804165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5804165).length < 2 ^ (prefixWord ++ tailWord_5804165).sum := by decide
  have hdescent : baseEnd_5804165 < baseStart_5804165 := by decide
  rcases family_descends (prefixWord ++ tailWord_5804165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5804242 : List Nat := [3, 2, 2, 2, 1, 2, 3, 2, 1, 5]
def baseStart_5804242 : Nat := 118140960795 + 5804242 * 2 ^ 59
def prefixEnd_5804242 : Nat := 4983230072969 + 3 ^ 40 * 5804242 * 2
def baseEnd_5804242 : Nat := 993455327004595036727261

theorem tailTrace_5804242 : CollatzResearch.WordTrace tailWord_5804242 prefixEnd_5804242 993455327004595036727261 := by
  unfold tailWord_5804242
  simp only [CollatzResearch.WordTrace]
  refine ⟨52924524359557498614607745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141132064958819996305620653 52924524359557498614607745)
  ·
    refine ⟨39693393269668123960955809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52924524359557498614607745 39693393269668123960955809)
    ·
      refine ⟨29770044952251092970716857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39693393269668123960955809 29770044952251092970716857)
      ·
        refine ⟨22327533714188319728037643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29770044952251092970716857 22327533714188319728037643)
        ·
          refine ⟨33491300571282479592056465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22327533714188319728037643 33491300571282479592056465)
          ·
            refine ⟨25118475428461859694042349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33491300571282479592056465 25118475428461859694042349)
            ·
              refine ⟨9419428285673197385265881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25118475428461859694042349 9419428285673197385265881)
              ·
                refine ⟨7064571214254898038949411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9419428285673197385265881 7064571214254898038949411)
                ·
                  refine ⟨10596856821382347058424117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7064571214254898038949411 10596856821382347058424117)
                  ·
                    refine ⟨993455327004595036727261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10596856821382347058424117 993455327004595036727261)
                    ·
                      rfl

theorem cell23_5804242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_5804242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5804242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5804242 prefixEnd_5804242 := by exact prefixLift 5804242
  have htrace : WordTrace (prefixWord ++ tailWord_5804242) baseStart_5804242 baseEnd_5804242 := by
    simpa [prefixWord, tailWord_5804242, baseEnd_5804242] using wordTrace_append hprefix tailTrace_5804242
  have hstable : (prefixWord ++ tailWord_5804242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5804242).length < 2 ^ (prefixWord ++ tailWord_5804242).sum := by decide
  have hdescent : baseEnd_5804242 < baseStart_5804242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5804242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5804288 : List Nat := [2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 6]
def baseStart_5804288 : Nat := 118140960795 + 5804288 * 2 ^ 59
def prefixEnd_5804288 : Nat := 4983230072969 + 3 ^ 40 * 5804288 * 2
def baseEnd_5804288 : Nat := 2980389601123891930206571

theorem tailTrace_5804288 : CollatzResearch.WordTrace tailWord_5804288 prefixEnd_5804288 2980389601123891930206571 := by
  unfold tailWord_5804288
  simp only [CollatzResearch.WordTrace]
  refine ⟨105849887598031672157302759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141133183464042229543070345 105849887598031672157302759)
  ·
    refine ⟨158774831397047508235954139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105849887598031672157302759 158774831397047508235954139)
    ·
      refine ⟨238162247095571262353931209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158774831397047508235954139 238162247095571262353931209)
      ·
        refine ⟨178621685321678446765448407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238162247095571262353931209 178621685321678446765448407)
        ·
          refine ⟨267932527982517670148172611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178621685321678446765448407 267932527982517670148172611)
          ·
            refine ⟨401898791973776505222258917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267932527982517670148172611 401898791973776505222258917)
            ·
              refine ⟨75356023495083094729173547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 401898791973776505222258917 75356023495083094729173547)
              ·
                refine ⟨113034035242624642093760321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75356023495083094729173547 113034035242624642093760321)
                ·
                  refine ⟨84775526431968481570320241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113034035242624642093760321 84775526431968481570320241)
                  ·
                    refine ⟨63581644823976361177740181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 84775526431968481570320241 63581644823976361177740181)
                    ·
                      refine ⟨2980389601123891930206571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63581644823976361177740181 2980389601123891930206571)
                      ·
                        rfl

theorem cell23_5804288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 6].length) (baseStart_5804288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5804288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5804288 prefixEnd_5804288 := by exact prefixLift 5804288
  have htrace : WordTrace (prefixWord ++ tailWord_5804288) baseStart_5804288 baseEnd_5804288 := by
    simpa [prefixWord, tailWord_5804288, baseEnd_5804288] using wordTrace_append hprefix tailTrace_5804288
  have hstable : (prefixWord ++ tailWord_5804288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5804288).length < 2 ^ (prefixWord ++ tailWord_5804288).sum := by decide
  have hdescent : baseEnd_5804288 < baseStart_5804288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5804288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5804312 : List Nat := [2, 1, 2, 3, 1, 2, 2, 2, 4, 1, 3]
def baseStart_5804312 : Nat := 118140960795 + 5804312 * 2 ^ 59
def prefixEnd_5804312 : Nat := 4983230072969 + 3 ^ 40 * 5804312 * 2
def baseEnd_5804312 : Nat := 2980401924659599836306461

theorem tailTrace_5804312 : CollatzResearch.WordTrace tailWord_5804312 prefixEnd_5804312 2980401924659599836306461 := by
  unfold tailWord_5804312
  simp only [CollatzResearch.WordTrace]
  refine ⟨105850325273988198206739595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141133767031984264275652793 105850325273988198206739595)
  ·
    refine ⟨158775487910982297310109393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105850325273988198206739595 158775487910982297310109393)
    ·
      refine ⟨119081615933236722982582045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158775487910982297310109393 119081615933236722982582045)
      ·
        refine ⟨44655605974963771118468267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119081615933236722982582045 44655605974963771118468267)
        ·
          refine ⟨66983408962445656677702401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44655605974963771118468267 66983408962445656677702401)
          ·
            refine ⟨50237556721834242508276801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66983408962445656677702401 50237556721834242508276801)
            ·
              refine ⟨37678167541375681881207601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50237556721834242508276801 37678167541375681881207601)
              ·
                refine ⟨28258625656031761410905701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37678167541375681881207601 28258625656031761410905701)
                ·
                  refine ⟨5298492310505955264544819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28258625656031761410905701 5298492310505955264544819)
                  ·
                    refine ⟨7947738465758932896817229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5298492310505955264544819 7947738465758932896817229)
                    ·
                      refine ⟨2980401924659599836306461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7947738465758932896817229 2980401924659599836306461)
                      ·
                        rfl

theorem cell23_5804312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_5804312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5804312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5804312 prefixEnd_5804312 := by exact prefixLift 5804312
  have htrace : WordTrace (prefixWord ++ tailWord_5804312) baseStart_5804312 baseEnd_5804312 := by
    simpa [prefixWord, tailWord_5804312, baseEnd_5804312] using wordTrace_append hprefix tailTrace_5804312
  have hstable : (prefixWord ++ tailWord_5804312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5804312).length < 2 ^ (prefixWord ++ tailWord_5804312).sum := by decide
  have hdescent : baseEnd_5804312 < baseStart_5804312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5804312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5804346 : List Nat := [3, 1, 1, 1, 4, 3, 3, 1, 2, 1, 3]
def baseStart_5804346 : Nat := 118140960795 + 5804346 * 2 ^ 59
def prefixEnd_5804346 : Nat := 4983230072969 + 3 ^ 40 * 5804346 * 2
def baseEnd_5804346 : Nat := 2980419383001852703281305

theorem tailTrace_5804346 : CollatzResearch.WordTrace tailWord_5804346 prefixEnd_5804346 2980419383001852703281305 := by
  unfold tailWord_5804346
  simp only [CollatzResearch.WordTrace]
  refine ⟨52925472657463305055054223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141134593753235480146811261 52925472657463305055054223)
  ·
    refine ⟨79388208986194957582581335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52925472657463305055054223 79388208986194957582581335)
    ·
      refine ⟨119082313479292436373872003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79388208986194957582581335 119082313479292436373872003)
      ·
        refine ⟨178623470218938654560808005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119082313479292436373872003 178623470218938654560808005)
        ·
          refine ⟨33491900666050997730151501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 178623470218938654560808005 33491900666050997730151501)
          ·
            refine ⟨12559462749769124148806813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33491900666050997730151501 12559462749769124148806813)
            ·
              refine ⟨4709798531163421555802555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12559462749769124148806813 4709798531163421555802555)
              ·
                refine ⟨7064697796745132333703833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4709798531163421555802555 7064697796745132333703833)
                ·
                  refine ⟨5298523347558849250277875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7064697796745132333703833 5298523347558849250277875)
                  ·
                    refine ⟨7947785021338273875416813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5298523347558849250277875 7947785021338273875416813)
                    ·
                      refine ⟨2980419383001852703281305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7947785021338273875416813 2980419383001852703281305)
                      ·
                        rfl

theorem cell23_5804346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 1, 2, 1, 3].length) (baseStart_5804346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5804346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5804346 prefixEnd_5804346 := by exact prefixLift 5804346
  have htrace : WordTrace (prefixWord ++ tailWord_5804346) baseStart_5804346 baseEnd_5804346 := by
    simpa [prefixWord, tailWord_5804346, baseEnd_5804346] using wordTrace_append hprefix tailTrace_5804346
  have hstable : (prefixWord ++ tailWord_5804346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5804346).length < 2 ^ (prefixWord ++ tailWord_5804346).sum := by decide
  have hdescent : baseEnd_5804346 < baseStart_5804346 := by decide
  rcases family_descends (prefixWord ++ tailWord_5804346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5804352 : List Nat := [2, 1, 1, 2, 2, 1, 2, 5, 1, 4, 2]
def baseStart_5804352 : Nat := 118140960795 + 5804352 * 2 ^ 59
def prefixEnd_5804352 : Nat := 4983230072969 + 3 ^ 40 * 5804352 * 2
def baseEnd_5804352 : Nat := 2980422463885779679806277

theorem tailTrace_5804352 : CollatzResearch.WordTrace tailWord_5804352 prefixEnd_5804352 2980422463885779679806277 := by
  unfold tailWord_5804352
  simp only [CollatzResearch.WordTrace]
  refine ⟨105851054733915741622467655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141134739645220988829956873 105851054733915741622467655)
  ·
    refine ⟨158776582100873612433701483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105851054733915741622467655 158776582100873612433701483)
    ·
      refine ⟨238164873151310418650552225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158776582100873612433701483 238164873151310418650552225)
      ·
        refine ⟨178623654863482813987914169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238164873151310418650552225 178623654863482813987914169)
        ·
          refine ⟨133967741147612110490935627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178623654863482813987914169 133967741147612110490935627)
          ·
            refine ⟨200951611721418165736403441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133967741147612110490935627 200951611721418165736403441)
            ·
              refine ⟨150713708791063624302302581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200951611721418165736403441 150713708791063624302302581)
              ·
                refine ⟨14129410199162214778340867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 150713708791063624302302581 14129410199162214778340867)
                ·
                  refine ⟨21194115298743322167511301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14129410199162214778340867 21194115298743322167511301)
                  ·
                    refine ⟨3973896618514372906408369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21194115298743322167511301 3973896618514372906408369)
                    ·
                      refine ⟨2980422463885779679806277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3973896618514372906408369 2980422463885779679806277)
                      ·
                        rfl

theorem cell23_5804352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 1, 4, 2].length) (baseStart_5804352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5804352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5804352 prefixEnd_5804352 := by exact prefixLift 5804352
  have htrace : WordTrace (prefixWord ++ tailWord_5804352) baseStart_5804352 baseEnd_5804352 := by
    simpa [prefixWord, tailWord_5804352, baseEnd_5804352] using wordTrace_append hprefix tailTrace_5804352
  have hstable : (prefixWord ++ tailWord_5804352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5804352).length < 2 ^ (prefixWord ++ tailWord_5804352).sum := by decide
  have hdescent : baseEnd_5804352 < baseStart_5804352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5804352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5804355 : List Nat := [1, 1, 1, 3, 1, 3, 2, 2, 2, 4, 3]
def baseStart_5804355 : Nat := 118140960795 + 5804355 * 2 ^ 59
def prefixEnd_5804355 : Nat := 4983230072969 + 3 ^ 40 * 5804355 * 2
def baseEnd_5804355 : Nat := 2980424004327743168068763

theorem tailTrace_5804355 : CollatzResearch.WordTrace tailWord_5804355 prefixEnd_5804355 2980424004327743168068763 := by
  unfold tailWord_5804355
  simp only [CollatzResearch.WordTrace]
  refine ⟨211702218886820614757294519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141134812591213743171529679 211702218886820614757294519)
  ·
    refine ⟨317553328330230922135941779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211702218886820614757294519 317553328330230922135941779)
    ·
      refine ⟨476329992495346383203912669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317553328330230922135941779 476329992495346383203912669)
      ·
        refine ⟨178623747185754893701467251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 476329992495346383203912669 178623747185754893701467251)
        ·
          refine ⟨267935620778632340552200877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178623747185754893701467251 267935620778632340552200877)
          ·
            refine ⟨100475857791987127707075329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 267935620778632340552200877 100475857791987127707075329)
            ·
              refine ⟨75356893343990345780306497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100475857791987127707075329 75356893343990345780306497)
              ·
                refine ⟨56517670007992759335229873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75356893343990345780306497 56517670007992759335229873)
                ·
                  refine ⟨42388252505994569501422405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56517670007992759335229873 42388252505994569501422405)
                  ·
                    refine ⟨7947797344873981781516701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42388252505994569501422405 7947797344873981781516701)
                    ·
                      refine ⟨2980424004327743168068763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7947797344873981781516701 2980424004327743168068763)
                      ·
                        rfl

theorem cell23_5804355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 4, 3].length) (baseStart_5804355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5804355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5804355 prefixEnd_5804355 := by exact prefixLift 5804355
  have htrace : WordTrace (prefixWord ++ tailWord_5804355) baseStart_5804355 baseEnd_5804355 := by
    simpa [prefixWord, tailWord_5804355, baseEnd_5804355] using wordTrace_append hprefix tailTrace_5804355
  have hstable : (prefixWord ++ tailWord_5804355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5804355).length < 2 ^ (prefixWord ++ tailWord_5804355).sum := by decide
  have hdescent : baseEnd_5804355 < baseStart_5804355 := by decide
  rcases family_descends (prefixWord ++ tailWord_5804355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5804369 : List Nat := [1, 2, 2, 1, 4, 2, 1, 2, 4, 2, 2]
def baseStart_5804369 : Nat := 118140960795 + 5804369 * 2 ^ 59
def prefixEnd_5804369 : Nat := 4983230072969 + 3 ^ 40 * 5804369 * 2
def baseEnd_5804369 : Nat := 2980431193056906113293699

theorem tailTrace_5804369 : CollatzResearch.WordTrace tailWord_5804369 prefixEnd_5804369 2980431193056906113293699 := by
  unfold tailWord_5804369
  simp only [CollatzResearch.WordTrace]
  refine ⟨211702729508769895148304161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141135153005846596765536107 211702729508769895148304161)
  ·
    refine ⟨158777047131577421361228121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211702729508769895148304161 158777047131577421361228121)
    ·
      refine ⟨119082785348683066020921091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158777047131577421361228121 119082785348683066020921091)
      ·
        refine ⟨178624178023024599031381637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119082785348683066020921091 178624178023024599031381637)
        ·
          refine ⟨33492033379317112318384057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 178624178023024599031381637 33492033379317112318384057)
          ·
            refine ⟨25119025034487834238788043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33492033379317112318384057 25119025034487834238788043)
            ·
              refine ⟨37678537551731751358182065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25119025034487834238788043 37678537551731751358182065)
              ·
                refine ⟨28258903163798813518636549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37678537551731751358182065 28258903163798813518636549)
                ·
                  refine ⟨5298544343212277534744353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28258903163798813518636549 5298544343212277534744353)
                  ·
                    refine ⟨3973908257409208151058265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5298544343212277534744353 3973908257409208151058265)
                    ·
                      refine ⟨2980431193056906113293699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3973908257409208151058265 2980431193056906113293699)
                      ·
                        rfl

theorem cell23_5804369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 4, 2, 2].length) (baseStart_5804369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5804369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5804369 prefixEnd_5804369 := by exact prefixLift 5804369
  have htrace : WordTrace (prefixWord ++ tailWord_5804369) baseStart_5804369 baseEnd_5804369 := by
    simpa [prefixWord, tailWord_5804369, baseEnd_5804369] using wordTrace_append hprefix tailTrace_5804369
  have hstable : (prefixWord ++ tailWord_5804369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5804369).length < 2 ^ (prefixWord ++ tailWord_5804369).sum := by decide
  have hdescent : baseEnd_5804369 < baseStart_5804369 := by decide
  rcases family_descends (prefixWord ++ tailWord_5804369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5804372 : List Nat := [2, 4, 1, 1, 2, 3, 1, 1, 2, 1, 5]
def baseStart_5804372 : Nat := 118140960795 + 5804372 * 2 ^ 59
def prefixEnd_5804372 : Nat := 4983230072969 + 3 ^ 40 * 5804372 * 2
def baseEnd_5804372 : Nat := 2980432733498869601556185

theorem tailTrace_5804372 : CollatzResearch.WordTrace tailWord_5804372 prefixEnd_5804372 2980432733498869601556185 := by
  unfold tailWord_5804372
  simp only [CollatzResearch.WordTrace]
  refine ⟨105851419463879513330331685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141135225951839351107108913 105851419463879513330331685)
  ·
    refine ⟨19847141149477408749437191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105851419463879513330331685 19847141149477408749437191)
    ·
      refine ⟨29770711724216113124155787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19847141149477408749437191 29770711724216113124155787)
      ·
        refine ⟨44656067586324169686233681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29770711724216113124155787 44656067586324169686233681)
        ·
          refine ⟨33492050689743127264675261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44656067586324169686233681 33492050689743127264675261)
          ·
            refine ⟨12559519008653672724253223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33492050689743127264675261 12559519008653672724253223)
            ·
              refine ⟨18839278512980509086379835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12559519008653672724253223 18839278512980509086379835)
              ·
                refine ⟨28258917769470763629569753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18839278512980509086379835 28258917769470763629569753)
                ·
                  refine ⟨21194188327103072722177315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28258917769470763629569753 21194188327103072722177315)
                  ·
                    refine ⟨31791282490654609083265973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21194188327103072722177315 31791282490654609083265973)
                    ·
                      refine ⟨2980432733498869601556185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31791282490654609083265973 2980432733498869601556185)
                      ·
                        rfl

theorem cell23_5804372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_5804372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5804372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5804372 prefixEnd_5804372 := by exact prefixLift 5804372
  have htrace : WordTrace (prefixWord ++ tailWord_5804372) baseStart_5804372 baseEnd_5804372 := by
    simpa [prefixWord, tailWord_5804372, baseEnd_5804372] using wordTrace_append hprefix tailTrace_5804372
  have hstable : (prefixWord ++ tailWord_5804372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5804372).length < 2 ^ (prefixWord ++ tailWord_5804372).sum := by decide
  have hdescent : baseEnd_5804372 < baseStart_5804372 := by decide
  rcases family_descends (prefixWord ++ tailWord_5804372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5804386 : List Nat := [3, 3, 2, 1, 1, 2, 2, 1, 4, 2, 2]
def baseStart_5804386 : Nat := 118140960795 + 5804386 * 2 ^ 59
def prefixEnd_5804386 : Nat := 4983230072969 + 3 ^ 40 * 5804386 * 2
def baseEnd_5804386 : Nat := 2980439922228032546781121

theorem tailTrace_5804386 : CollatzResearch.WordTrace tailWord_5804386 prefixEnd_5804386 2980439922228032546781121 := by
  unfold tailWord_5804386
  simp only [CollatzResearch.WordTrace]
  refine ⟨52925837387427076762918253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141135566366472204701115341 52925837387427076762918253)
  ·
    refine ⟨19847189020285153786094345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52925837387427076762918253 19847189020285153786094345)
    ·
      refine ⟨14885391765213865339570759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19847189020285153786094345 14885391765213865339570759)
      ·
        refine ⟨22328087647820798009356139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14885391765213865339570759 22328087647820798009356139)
        ·
          refine ⟨33492131471731197014034209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22328087647820798009356139 33492131471731197014034209)
          ·
            refine ⟨25119098603798397760525657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33492131471731197014034209 25119098603798397760525657)
            ·
              refine ⟨18839323952848798320394243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25119098603798397760525657 18839323952848798320394243)
              ·
                refine ⟨28258985929273197480591365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18839323952848798320394243 28258985929273197480591365)
                ·
                  refine ⟨5298559861738724527610881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28258985929273197480591365 5298559861738724527610881)
                  ·
                    refine ⟨3973919896304043395708161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5298559861738724527610881 3973919896304043395708161)
                    ·
                      refine ⟨2980439922228032546781121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3973919896304043395708161 2980439922228032546781121)
                      ·
                        rfl

theorem cell23_5804386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_5804386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5804386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5804386 prefixEnd_5804386 := by exact prefixLift 5804386
  have htrace : WordTrace (prefixWord ++ tailWord_5804386) baseStart_5804386 baseEnd_5804386 := by
    simpa [prefixWord, tailWord_5804386, baseEnd_5804386] using wordTrace_append hprefix tailTrace_5804386
  have hstable : (prefixWord ++ tailWord_5804386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5804386).length < 2 ^ (prefixWord ++ tailWord_5804386).sum := by decide
  have hdescent : baseEnd_5804386 < baseStart_5804386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5804386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5804392 : List Nat := [2, 1, 4, 2, 2, 1, 3, 1, 7]
def baseStart_5804392 : Nat := 118140960795 + 5804392 * 2 ^ 59
def prefixEnd_5804392 : Nat := 4983230072969 + 3 ^ 40 * 5804392 * 2
def baseEnd_5804392 : Nat := 331160333679106613700677

theorem tailTrace_5804392 : CollatzResearch.WordTrace tailWord_5804392 prefixEnd_5804392 331160333679106613700677 := by
  unfold tailWord_5804392
  simp only [CollatzResearch.WordTrace]
  refine ⟨105851784193843285038195715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141135712258457713384260953 105851784193843285038195715)
  ·
    refine ⟨158777676290764927557293573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105851784193843285038195715 158777676290764927557293573)
    ·
      refine ⟨29770814304518423916992545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158777676290764927557293573 29770814304518423916992545)
      ·
        refine ⟨22328110728388817937744409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29770814304518423916992545 22328110728388817937744409)
        ·
          refine ⟨16746083046291613453308307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22328110728388817937744409 16746083046291613453308307)
          ·
            refine ⟨25119124569437420179962461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16746083046291613453308307 25119124569437420179962461)
            ·
              refine ⟨9419671713539032567485923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25119124569437420179962461 9419671713539032567485923)
              ·
                refine ⟨14129507570308548851228885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9419671713539032567485923 14129507570308548851228885)
                ·
                  refine ⟨331160333679106613700677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14129507570308548851228885 331160333679106613700677)
                  ·
                    rfl

theorem cell23_5804392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 7].length) (baseStart_5804392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5804392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5804392 prefixEnd_5804392 := by exact prefixLift 5804392
  have htrace : WordTrace (prefixWord ++ tailWord_5804392) baseStart_5804392 baseEnd_5804392 := by
    simpa [prefixWord, tailWord_5804392, baseEnd_5804392] using wordTrace_append hprefix tailTrace_5804392
  have hstable : (prefixWord ++ tailWord_5804392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5804392).length < 2 ^ (prefixWord ++ tailWord_5804392).sum := by decide
  have hdescent : baseEnd_5804392 < baseStart_5804392 := by decide
  rcases family_descends (prefixWord ++ tailWord_5804392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5804412 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 4, 5, 2]
def baseStart_5804412 : Nat := 118140960795 + 5804412 * 2 ^ 59
def prefixEnd_5804412 : Nat := 4983230072969 + 3 ^ 40 * 5804412 * 2
def baseEnd_5804412 : Nat := 2980453272725049445056001

theorem tailTrace_5804412 : CollatzResearch.WordTrace tailWord_5804412 prefixEnd_5804412 2980453272725049445056001 := by
  unfold tailWord_5804412
  simp only [CollatzResearch.WordTrace]
  refine ⟨105852148923807056746059745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141136198565076075661412993 105852148923807056746059745)
  ·
    refine ⟨79389111692855292559544809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105852148923807056746059745 79389111692855292559544809)
    ·
      refine ⟨59541833769641469419658607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79389111692855292559544809 59541833769641469419658607)
      ·
        refine ⟨89312750654462204129487911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59541833769641469419658607 89312750654462204129487911)
        ·
          refine ⟨133969125981693306194231867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89312750654462204129487911 133969125981693306194231867)
          ·
            refine ⟨200953688972539959291347801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133969125981693306194231867 200953688972539959291347801)
            ·
              refine ⟨150715266729404969468510851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200953688972539959291347801 150715266729404969468510851)
              ·
                refine ⟨226072900094107454202766277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150715266729404969468510851 226072900094107454202766277)
                ·
                  refine ⟨42388668767645147663018677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 226072900094107454202766277 42388668767645147663018677)
                  ·
                    refine ⟨3973937696966732593408001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42388668767645147663018677 3973937696966732593408001)
                    ·
                      refine ⟨2980453272725049445056001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3973937696966732593408001 2980453272725049445056001)
                      ·
                        rfl

theorem cell23_5804412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 4, 5, 2].length) (baseStart_5804412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5804412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5804412 prefixEnd_5804412 := by exact prefixLift 5804412
  have htrace : WordTrace (prefixWord ++ tailWord_5804412) baseStart_5804412 baseEnd_5804412 := by
    simpa [prefixWord, tailWord_5804412, baseEnd_5804412] using wordTrace_append hprefix tailTrace_5804412
  have hstable : (prefixWord ++ tailWord_5804412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5804412).length < 2 ^ (prefixWord ++ tailWord_5804412).sum := by decide
  have hdescent : baseEnd_5804412 < baseStart_5804412 := by decide
  rcases family_descends (prefixWord ++ tailWord_5804412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5804446 : List Nat := [4, 3, 1, 2, 1, 1, 1, 1, 2, 5, 2]
def baseStart_5804446 : Nat := 118140960795 + 5804446 * 2 ^ 59
def prefixEnd_5804446 : Nat := 4983230072969 + 3 ^ 40 * 5804446 * 2
def baseEnd_5804446 : Nat := 2980470731067302312030845

theorem tailTrace_5804446 : CollatzResearch.WordTrace tailWord_5804446 prefixEnd_5804446 2980470731067302312030845 := by
  unfold tailWord_5804446
  simp only [CollatzResearch.WordTrace]
  refine ⟨26463192241186367162357149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141137025286327291532571461 26463192241186367162357149)
  ·
    refine ⟨9923697090444887685883931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26463192241186367162357149 9923697090444887685883931)
    ·
      refine ⟨14885545635667331528825897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9923697090444887685883931 14885545635667331528825897)
      ·
        refine ⟨11164159226750498646619423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14885545635667331528825897 11164159226750498646619423)
        ·
          refine ⟨16746238840125747969929135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11164159226750498646619423 16746238840125747969929135)
          ·
            refine ⟨25119358260188621954893703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16746238840125747969929135 25119358260188621954893703)
            ·
              refine ⟨37679037390282932932340555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25119358260188621954893703 37679037390282932932340555)
              ·
                refine ⟨56518556085424399398510833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37679037390282932932340555 56518556085424399398510833)
                ·
                  refine ⟨42388917064068299548883125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56518556085424399398510833 42388917064068299548883125)
                  ·
                    refine ⟨3973960974756403082707793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42388917064068299548883125 3973960974756403082707793)
                    ·
                      refine ⟨2980470731067302312030845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3973960974756403082707793 2980470731067302312030845)
                      ·
                        rfl

theorem cell23_5804446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_5804446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5804446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5804446 prefixEnd_5804446 := by exact prefixLift 5804446
  have htrace : WordTrace (prefixWord ++ tailWord_5804446) baseStart_5804446 baseEnd_5804446 := by
    simpa [prefixWord, tailWord_5804446, baseEnd_5804446] using wordTrace_append hprefix tailTrace_5804446
  have hstable : (prefixWord ++ tailWord_5804446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5804446).length < 2 ^ (prefixWord ++ tailWord_5804446).sum := by decide
  have hdescent : baseEnd_5804446 < baseStart_5804446 := by decide
  rcases family_descends (prefixWord ++ tailWord_5804446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5804476 : List Nat := [2, 2, 2, 4, 1, 3, 1, 1, 2, 1, 4]
def baseStart_5804476 : Nat := 118140960795 + 5804476 * 2 ^ 59
def prefixEnd_5804476 : Nat := 4983230072969 + 3 ^ 40 * 5804476 * 2
def baseEnd_5804476 : Nat := 2980486135486937194655707

theorem tailTrace_5804476 : CollatzResearch.WordTrace tailWord_5804476 prefixEnd_5804476 2980486135486937194655707 := by
  unfold tailWord_5804476
  simp only [CollatzResearch.WordTrace]
  refine ⟨105853316059691126211224641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141137754746254834948299521 105853316059691126211224641)
  ·
    refine ⟨79389987044768344658418481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105853316059691126211224641 79389987044768344658418481)
    ·
      refine ⟨59542490283576258493813861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79389987044768344658418481 59542490283576258493813861)
      ·
        refine ⟨11164216928170548467590099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59542490283576258493813861 11164216928170548467590099)
        ·
          refine ⟨16746325392255822701385149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11164216928170548467590099 16746325392255822701385149)
          ·
            refine ⟨6279872022095933513019431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16746325392255822701385149 6279872022095933513019431)
            ·
              refine ⟨9419808033143900269529147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6279872022095933513019431 9419808033143900269529147)
              ·
                refine ⟨14129712049715850404293721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9419808033143900269529147 14129712049715850404293721)
                ·
                  refine ⟨10597284037286887803220291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14129712049715850404293721 10597284037286887803220291)
                  ·
                    refine ⟨15895926055930331704830437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10597284037286887803220291 15895926055930331704830437)
                    ·
                      refine ⟨2980486135486937194655707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15895926055930331704830437 2980486135486937194655707)
                      ·
                        rfl

theorem cell23_5804476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_5804476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5804476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5804476 prefixEnd_5804476 := by exact prefixLift 5804476
  have htrace : WordTrace (prefixWord ++ tailWord_5804476) baseStart_5804476 baseEnd_5804476 := by
    simpa [prefixWord, tailWord_5804476, baseEnd_5804476] using wordTrace_append hprefix tailTrace_5804476
  have hstable : (prefixWord ++ tailWord_5804476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5804476).length < 2 ^ (prefixWord ++ tailWord_5804476).sum := by decide
  have hdescent : baseEnd_5804476 < baseStart_5804476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5804476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5804485 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 5, 2, 6]
def baseStart_5804485 : Nat := 118140960795 + 5804485 * 2 ^ 59
def prefixEnd_5804485 : Nat := 4983230072969 + 3 ^ 40 * 5804485 * 2
def baseEnd_5804485 : Nat := 2980490756812827659443165

theorem tailTrace_5804485 : CollatzResearch.WordTrace tailWord_5804485 prefixEnd_5804485 2980490756812827659443165 := by
  unfold tailWord_5804485
  simp only [CollatzResearch.WordTrace]
  refine ⟨211706960376349646959526909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141137973584233097973017939 211706960376349646959526909)
  ·
    refine ⟨79390110141131117609822591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211706960376349646959526909 79390110141131117609822591)
    ·
      refine ⟨119085165211696676414733887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79390110141131117609822591 119085165211696676414733887)
      ·
        refine ⟨178627747817545014622100831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119085165211696676414733887 178627747817545014622100831)
        ·
          refine ⟨267941621726317521933151247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178627747817545014622100831 267941621726317521933151247)
          ·
            refine ⟨401912432589476282899726871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267941621726317521933151247 401912432589476282899726871)
            ·
              refine ⟨602868648884214424349590307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 401912432589476282899726871 602868648884214424349590307)
              ·
                refine ⟨904302973326321636524385461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 602868648884214424349590307 904302973326321636524385461)
                ·
                  refine ⟨84778403749342653424161137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 904302973326321636524385461 84778403749342653424161137)
                  ·
                    refine ⟨63583802812006990068120853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 84778403749342653424161137 63583802812006990068120853)
                    ·
                      refine ⟨2980490756812827659443165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63583802812006990068120853 2980490756812827659443165)
                      ·
                        rfl

theorem cell23_5804485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 2, 6].length) (baseStart_5804485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5804485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5804485 prefixEnd_5804485 := by exact prefixLift 5804485
  have htrace : WordTrace (prefixWord ++ tailWord_5804485) baseStart_5804485 baseEnd_5804485 := by
    simpa [prefixWord, tailWord_5804485, baseEnd_5804485] using wordTrace_append hprefix tailTrace_5804485
  have hstable : (prefixWord ++ tailWord_5804485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5804485).length < 2 ^ (prefixWord ++ tailWord_5804485).sum := by decide
  have hdescent : baseEnd_5804485 < baseStart_5804485 := by decide
  rcases family_descends (prefixWord ++ tailWord_5804485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5804519 : List Nat := [1, 1, 5, 2, 1, 1, 1, 1, 3, 5, 2]
def baseStart_5804519 : Nat := 118140960795 + 5804519 * 2 ^ 59
def prefixEnd_5804519 : Nat := 4983230072969 + 3 ^ 40 * 5804519 * 2
def baseEnd_5804519 : Nat := 2980508215155080526418009

theorem tailTrace_5804519 : CollatzResearch.WordTrace tailWord_5804519 prefixEnd_5804519 2980508215155080526418009 := by
  unfold tailWord_5804519
  simp only [CollatzResearch.WordTrace]
  refine ⟨211708200458226470766264611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141138800305484313844176407 211708200458226470766264611)
  ·
    refine ⟨317562300687339706149396917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211708200458226470766264611 317562300687339706149396917)
    ·
      refine ⟨29771465689438097451505961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 317562300687339706149396917 29771465689438097451505961)
      ·
        refine ⟨22328599267078573088629471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29771465689438097451505961 22328599267078573088629471)
        ·
          refine ⟨33492898900617859632944207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22328599267078573088629471 33492898900617859632944207)
          ·
            refine ⟨50239348350926789449416311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33492898900617859632944207 50239348350926789449416311)
            ·
              refine ⟨75359022526390184174124467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50239348350926789449416311 75359022526390184174124467)
              ·
                refine ⟨113038533789585276261186701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75359022526390184174124467 113038533789585276261186701)
                ·
                  refine ⟨42389450171094478597945013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113038533789585276261186701 42389450171094478597945013)
                  ·
                    refine ⟨3974010953540107368557345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42389450171094478597945013 3974010953540107368557345)
                    ·
                      refine ⟨2980508215155080526418009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3974010953540107368557345 2980508215155080526418009)
                      ·
                        rfl

theorem cell23_5804519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_5804519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5804519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5804519 prefixEnd_5804519 := by exact prefixLift 5804519
  have htrace : WordTrace (prefixWord ++ tailWord_5804519) baseStart_5804519 baseEnd_5804519 := by
    simpa [prefixWord, tailWord_5804519, baseEnd_5804519] using wordTrace_append hprefix tailTrace_5804519
  have hstable : (prefixWord ++ tailWord_5804519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5804519).length < 2 ^ (prefixWord ++ tailWord_5804519).sum := by decide
  have hdescent : baseEnd_5804519 < baseStart_5804519 := by decide
  rcases family_descends (prefixWord ++ tailWord_5804519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5804526 : List Nat := [4, 1, 2, 1, 2, 2, 2, 2, 3, 1, 3]
def baseStart_5804526 : Nat := 118140960795 + 5804526 * 2 ^ 59
def prefixEnd_5804526 : Nat := 4983230072969 + 3 ^ 40 * 5804526 * 2
def baseEnd_5804526 : Nat := 2980511809519661999030477

theorem tailTrace_5804526 : CollatzResearch.WordTrace tailWord_5804526 prefixEnd_5804526 2980511809519661999030477 := by
  unfold tailWord_5804526
  simp only [CollatzResearch.WordTrace]
  refine ⟨26463556971150138870221179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141138970512800740641179621 26463556971150138870221179)
  ·
    refine ⟨39695335456725208305331769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26463556971150138870221179 39695335456725208305331769)
    ·
      refine ⟨29771501592543906228998827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39695335456725208305331769 29771501592543906228998827)
      ·
        refine ⟨44657252388815859343498241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29771501592543906228998827 44657252388815859343498241)
        ·
          refine ⟨33492939291611894507623681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44657252388815859343498241 33492939291611894507623681)
          ·
            refine ⟨25119704468708920880717761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33492939291611894507623681 25119704468708920880717761)
            ·
              refine ⟨18839778351531690660538321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25119704468708920880717761 18839778351531690660538321)
              ·
                refine ⟨14129833763648767995403741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18839778351531690660538321 14129833763648767995403741)
                ·
                  refine ⟨5298687661368287998276403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14129833763648767995403741 5298687661368287998276403)
                  ·
                    refine ⟨7948031492052431997414605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5298687661368287998276403 7948031492052431997414605)
                    ·
                      refine ⟨2980511809519661999030477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7948031492052431997414605 2980511809519661999030477)
                      ·
                        rfl

theorem cell23_5804526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_5804526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5804526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5804526 prefixEnd_5804526 := by exact prefixLift 5804526
  have htrace : WordTrace (prefixWord ++ tailWord_5804526) baseStart_5804526 baseEnd_5804526 := by
    simpa [prefixWord, tailWord_5804526, baseEnd_5804526] using wordTrace_append hprefix tailTrace_5804526
  have hstable : (prefixWord ++ tailWord_5804526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5804526).length < 2 ^ (prefixWord ++ tailWord_5804526).sum := by decide
  have hdescent : baseEnd_5804526 < baseStart_5804526 := by decide
  rcases family_descends (prefixWord ++ tailWord_5804526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5804529 : List Nat := [1, 2, 2, 2, 3, 1, 4, 2, 1, 5]
def baseStart_5804529 : Nat := 118140960795 + 5804529 * 2 ^ 59
def prefixEnd_5804529 : Nat := 4983230072969 + 3 ^ 40 * 5804529 * 2
def baseEnd_5804529 : Nat := 993504449987208495764321

theorem tailTrace_5804529 : CollatzResearch.WordTrace tailWord_5804529 prefixEnd_5804529 993504449987208495764321 := by
  unfold tailWord_5804529
  simp only [CollatzResearch.WordTrace]
  refine ⟨211708565188190242474128641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141139043458793494982752427 211708565188190242474128641)
  ·
    refine ⟨158781423891142681855596481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211708565188190242474128641 158781423891142681855596481)
    ·
      refine ⟨119086067918357011391697361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158781423891142681855596481 119086067918357011391697361)
      ·
        refine ⟨89314550938767758543773021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119086067918357011391697361 89314550938767758543773021)
        ·
          refine ⟨33492956602037909453914883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89314550938767758543773021 33492956602037909453914883)
          ·
            refine ⟨50239434903056864180872325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33492956602037909453914883 50239434903056864180872325)
            ·
              refine ⟨9419894044323162033913561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50239434903056864180872325 9419894044323162033913561)
              ·
                refine ⟨7064920533242371525435171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9419894044323162033913561 7064920533242371525435171)
                ·
                  refine ⟨10597380799863557288152757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7064920533242371525435171 10597380799863557288152757)
                  ·
                    refine ⟨993504449987208495764321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10597380799863557288152757 993504449987208495764321)
                    ·
                      rfl

theorem cell23_5804529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 2, 1, 5].length) (baseStart_5804529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5804529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5804529 prefixEnd_5804529 := by exact prefixLift 5804529
  have htrace : WordTrace (prefixWord ++ tailWord_5804529) baseStart_5804529 baseEnd_5804529 := by
    simpa [prefixWord, tailWord_5804529, baseEnd_5804529] using wordTrace_append hprefix tailTrace_5804529
  have hstable : (prefixWord ++ tailWord_5804529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5804529).length < 2 ^ (prefixWord ++ tailWord_5804529).sum := by decide
  have hdescent : baseEnd_5804529 < baseStart_5804529 := by decide
  rcases family_descends (prefixWord ++ tailWord_5804529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5804549 : List Nat := [1, 3, 1, 1, 2, 2, 4, 3, 1, 1, 4]
def baseStart_5804549 : Nat := 118140960795 + 5804549 * 2 ^ 59
def prefixEnd_5804549 : Nat := 4983230072969 + 3 ^ 40 * 5804549 * 2
def baseEnd_5804549 : Nat := 2980523619574715409042871

theorem tailTrace_5804549 : CollatzResearch.WordTrace tailWord_5804549 prefixEnd_5804549 2980523619574715409042871 := by
  unfold tailWord_5804549
  simp only [CollatzResearch.WordTrace]
  refine ⟨211709294648117785889856701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141139529765411857259904467 211709294648117785889856701)
  ·
    refine ⟨79390985493044169708696263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211709294648117785889856701 79390985493044169708696263)
    ·
      refine ⟨119086478239566254563044395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79390985493044169708696263 119086478239566254563044395)
      ·
        refine ⟨178629717359349381844566593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119086478239566254563044395 178629717359349381844566593)
        ·
          refine ⟨133972288019512036383424945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178629717359349381844566593 133972288019512036383424945)
          ·
            refine ⟨100479216014634027287568709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133972288019512036383424945 100479216014634027287568709)
            ·
              refine ⟨18839853002743880116419133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100479216014634027287568709 18839853002743880116419133)
              ·
                refine ⟨7064944876028955043657175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18839853002743880116419133 7064944876028955043657175)
                ·
                  refine ⟨10597417314043432565485763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7064944876028955043657175 10597417314043432565485763)
                  ·
                    refine ⟨15896125971065148848228645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10597417314043432565485763 15896125971065148848228645)
                    ·
                      refine ⟨2980523619574715409042871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15896125971065148848228645 2980523619574715409042871)
                      ·
                        rfl

theorem cell23_5804549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 3, 1, 1, 4].length) (baseStart_5804549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5804549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5804549 prefixEnd_5804549 := by exact prefixLift 5804549
  have htrace : WordTrace (prefixWord ++ tailWord_5804549) baseStart_5804549 baseEnd_5804549 := by
    simpa [prefixWord, tailWord_5804549, baseEnd_5804549] using wordTrace_append hprefix tailTrace_5804549
  have hstable : (prefixWord ++ tailWord_5804549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5804549).length < 2 ^ (prefixWord ++ tailWord_5804549).sum := by decide
  have hdescent : baseEnd_5804549 < baseStart_5804549 := by decide
  rcases family_descends (prefixWord ++ tailWord_5804549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5804572 : List Nat := [2, 2, 3, 1, 2, 2, 1, 10]
def baseStart_5804572 : Nat := 118140960795 + 5804572 * 2 ^ 59
def prefixEnd_5804572 : Nat := 4983230072969 + 3 ^ 40 * 5804572 * 2
def baseEnd_5804572 : Nat := 110390201097398845150195

theorem tailTrace_5804572 : CollatzResearch.WordTrace tailWord_5804572 prefixEnd_5804572 110390201097398845150195 := by
  unfold tailWord_5804572
  simp only [CollatzResearch.WordTrace]
  refine ⟨105855066763517230408971985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141140089018022973878629313 105855066763517230408971985)
  ·
    refine ⟨79391300072637922806728989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105855066763517230408971985 79391300072637922806728989)
    ·
      refine ⟨29771737527239221052523371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79391300072637922806728989 29771737527239221052523371)
      ·
        refine ⟨44657606290858831578785057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29771737527239221052523371 44657606290858831578785057)
        ·
          refine ⟨33493204718144123684088793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44657606290858831578785057 33493204718144123684088793)
          ·
            refine ⟨25119903538608092763066595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33493204718144123684088793 25119903538608092763066595)
            ·
              refine ⟨37679855307912139144599893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25119903538608092763066595 37679855307912139144599893)
              ·
                refine ⟨110390201097398845150195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 37679855307912139144599893 110390201097398845150195)
                ·
                  rfl

theorem cell23_5804572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 10].length) (baseStart_5804572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5804572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5804572 prefixEnd_5804572 := by exact prefixLift 5804572
  have htrace : WordTrace (prefixWord ++ tailWord_5804572) baseStart_5804572 baseEnd_5804572 := by
    simpa [prefixWord, tailWord_5804572, baseEnd_5804572] using wordTrace_append hprefix tailTrace_5804572
  have hstable : (prefixWord ++ tailWord_5804572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5804572).length < 2 ^ (prefixWord ++ tailWord_5804572).sum := by decide
  have hdescent : baseEnd_5804572 < baseStart_5804572 := by decide
  rcases family_descends (prefixWord ++ tailWord_5804572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5804580 : List Nat := [2, 3, 1, 5, 2, 1, 1, 2, 1, 5]
def baseStart_5804580 : Nat := 118140960795 + 5804580 * 2 ^ 59
def prefixEnd_5804580 : Nat := 4983230072969 + 3 ^ 40 * 5804580 * 2
def baseEnd_5804580 : Nat := 993513179158334929251743

theorem tailTrace_5804580 : CollatzResearch.WordTrace tailWord_5804580 prefixEnd_5804580 993513179158334929251743 := by
  unfold tailWord_5804580
  simp only [CollatzResearch.WordTrace]
  refine ⟨105855212655502739092117597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141140283540670318789490129 105855212655502739092117597)
  ·
    refine ⟨39695704745813527159544099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105855212655502739092117597 39695704745813527159544099)
    ·
      refine ⟨59543557118720290739316149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39695704745813527159544099 59543557118720290739316149)
      ·
        refine ⟨5582208479880027256810889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59543557118720290739316149 5582208479880027256810889)
        ·
          refine ⟨4186656359910020442608167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5582208479880027256810889 4186656359910020442608167)
          ·
            refine ⟨6279984539865030663912251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4186656359910020442608167 6279984539865030663912251)
            ·
              refine ⟨9419976809797545995868377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6279984539865030663912251 9419976809797545995868377)
              ·
                refine ⟨7064982607348159496901283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9419976809797545995868377 7064982607348159496901283)
                ·
                  refine ⟨10597473911022239245351925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7064982607348159496901283 10597473911022239245351925)
                  ·
                    refine ⟨993513179158334929251743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10597473911022239245351925 993513179158334929251743)
                    ·
                      rfl

theorem cell23_5804580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 2, 1, 5].length) (baseStart_5804580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5804580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5804580 prefixEnd_5804580 := by exact prefixLift 5804580
  have htrace : WordTrace (prefixWord ++ tailWord_5804580) baseStart_5804580 baseEnd_5804580 := by
    simpa [prefixWord, tailWord_5804580, baseEnd_5804580] using wordTrace_append hprefix tailTrace_5804580
  have hstable : (prefixWord ++ tailWord_5804580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5804580).length < 2 ^ (prefixWord ++ tailWord_5804580).sum := by decide
  have hdescent : baseEnd_5804580 < baseStart_5804580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5804580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5804583 : List Nat := [1, 1, 7, 2, 1, 1, 1, 1, 3, 1, 4]
def baseStart_5804583 : Nat := 118140960795 + 5804583 * 2 ^ 59
def prefixEnd_5804583 : Nat := 4983230072969 + 3 ^ 40 * 5804583 * 2
def baseEnd_5804583 : Nat := 2980541077916968276017715

theorem tailTrace_5804583 : CollatzResearch.WordTrace tailWord_5804583 prefixEnd_5804583 2980541077916968276017715 := by
  unfold tailWord_5804583
  simp only [CollatzResearch.WordTrace]
  refine ⟨211710534729994609696594403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141140356486663073131062935 211710534729994609696594403)
  ·
    refine ⟨317565802094991914544891605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211710534729994609696594403 317565802094991914544891605)
    ·
      refine ⟨7442948486601372997145897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 317565802094991914544891605 7442948486601372997145897)
      ·
        refine ⟨5582211364951029747859423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7442948486601372997145897 5582211364951029747859423)
        ·
          refine ⟨8373317047426544621789135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5582211364951029747859423 8373317047426544621789135)
          ·
            refine ⟨12559975571139816932683703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8373317047426544621789135 12559975571139816932683703)
            ·
              refine ⟨18839963356709725399025555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12559975571139816932683703 18839963356709725399025555)
              ·
                refine ⟨28259945035064588098538333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18839963356709725399025555 28259945035064588098538333)
                ·
                  refine ⟨10597479388149220536951875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28259945035064588098538333 10597479388149220536951875)
                  ·
                    refine ⟨15896219082223830805427813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10597479388149220536951875 15896219082223830805427813)
                    ·
                      refine ⟨2980541077916968276017715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15896219082223830805427813 2980541077916968276017715)
                      ·
                        rfl

theorem cell23_5804583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_5804583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5804583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5804583 prefixEnd_5804583 := by exact prefixLift 5804583
  have htrace : WordTrace (prefixWord ++ tailWord_5804583) baseStart_5804583 baseEnd_5804583 := by
    simpa [prefixWord, tailWord_5804583, baseEnd_5804583] using wordTrace_append hprefix tailTrace_5804583
  have hstable : (prefixWord ++ tailWord_5804583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5804583).length < 2 ^ (prefixWord ++ tailWord_5804583).sum := by decide
  have hdescent : baseEnd_5804583 < baseStart_5804583 := by decide
  rcases family_descends (prefixWord ++ tailWord_5804583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5804586 : List Nat := [3, 1, 4, 1, 1, 3, 1, 1, 3, 2, 3]
def baseStart_5804586 : Nat := 118140960795 + 5804586 * 2 ^ 59
def prefixEnd_5804586 : Nat := 4983230072969 + 3 ^ 40 * 5804586 * 2
def baseEnd_5804586 : Nat := 2980542618358931764280201

theorem tailTrace_5804586 : CollatzResearch.WordTrace tailWord_5804586 prefixEnd_5804586 2980542618358931764280201 := by
  unfold tailWord_5804586
  simp only [CollatzResearch.WordTrace]
  refine ⟨52927661037245935302238403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141140429432655827472635741 52927661037245935302238403)
  ·
    refine ⟨79391491555868902953357605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52927661037245935302238403 79391491555868902953357605)
    ·
      refine ⟨14885904666725419303754551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79391491555868902953357605 14885904666725419303754551)
      ·
        refine ⟨22328857000088128955631827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14885904666725419303754551 22328857000088128955631827)
        ·
          refine ⟨33493285500132193433447741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22328857000088128955631827 33493285500132193433447741)
          ·
            refine ⟨12559982062549572537542903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33493285500132193433447741 12559982062549572537542903)
            ·
              refine ⟨18839973093824358806314355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12559982062549572537542903 18839973093824358806314355)
              ·
                refine ⟨28259959640736538209471533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18839973093824358806314355 28259959640736538209471533)
                ·
                  refine ⟨10597484865276201828551825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28259959640736538209471533 10597484865276201828551825)
                  ·
                    refine ⟨7948113648957151371413869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10597484865276201828551825 7948113648957151371413869)
                    ·
                      refine ⟨2980542618358931764280201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7948113648957151371413869 2980542618358931764280201)
                      ·
                        rfl

theorem cell23_5804586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_5804586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5804586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5804586 prefixEnd_5804586 := by exact prefixLift 5804586
  have htrace : WordTrace (prefixWord ++ tailWord_5804586) baseStart_5804586 baseEnd_5804586 := by
    simpa [prefixWord, tailWord_5804586, baseEnd_5804586] using wordTrace_append hprefix tailTrace_5804586
  have hstable : (prefixWord ++ tailWord_5804586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5804586).length < 2 ^ (prefixWord ++ tailWord_5804586).sum := by decide
  have hdescent : baseEnd_5804586 < baseStart_5804586 := by decide
  rcases family_descends (prefixWord ++ tailWord_5804586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5804599 : List Nat := [1, 1, 3, 1, 2, 3, 3, 2, 1, 3, 3]
def baseStart_5804599 : Nat := 118140960795 + 5804599 * 2 ^ 59
def prefixEnd_5804599 : Nat := 4983230072969 + 3 ^ 40 * 5804599 * 2
def baseEnd_5804599 : Nat := 2980549293607440213417641

theorem tailTrace_5804599 : CollatzResearch.WordTrace tailWord_5804599 prefixEnd_5804599 2980549293607440213417641 := by
  unfold tailWord_5804599
  simp only [CollatzResearch.WordTrace]
  refine ⟨211711118297936644429176851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141140745531957762952784567 211711118297936644429176851)
  ·
    refine ⟨317566677446904966643765277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211711118297936644429176851 317566677446904966643765277)
    ·
      refine ⟨119087504042589362491411979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 317566677446904966643765277 119087504042589362491411979)
      ·
        refine ⟨178631256063884043737117969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119087504042589362491411979 178631256063884043737117969)
        ·
          refine ⟨133973442047913032802838477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178631256063884043737117969 133973442047913032802838477)
          ·
            refine ⟨50240040767967387301064429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133973442047913032802838477 50240040767967387301064429)
            ·
              refine ⟨18840015287987770237899161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50240040767967387301064429 18840015287987770237899161)
              ·
                refine ⟨14130011465990827678424371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18840015287987770237899161 14130011465990827678424371)
                ·
                  refine ⟨21195017198986241517636557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14130011465990827678424371 21195017198986241517636557)
                  ·
                    refine ⟨7948131449619840569113709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21195017198986241517636557 7948131449619840569113709)
                    ·
                      refine ⟨2980549293607440213417641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7948131449619840569113709 2980549293607440213417641)
                      ·
                        rfl

theorem cell23_5804599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 3, 3].length) (baseStart_5804599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5804599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5804599 prefixEnd_5804599 := by exact prefixLift 5804599
  have htrace : WordTrace (prefixWord ++ tailWord_5804599) baseStart_5804599 baseEnd_5804599 := by
    simpa [prefixWord, tailWord_5804599, baseEnd_5804599] using wordTrace_append hprefix tailTrace_5804599
  have hstable : (prefixWord ++ tailWord_5804599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5804599).length < 2 ^ (prefixWord ++ tailWord_5804599).sum := by decide
  have hdescent : baseEnd_5804599 < baseStart_5804599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5804599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5804606 : List Nat := [4, 2, 1, 4, 2, 10]
def baseStart_5804606 : Nat := 118140960795 + 5804606 * 2 ^ 59
def prefixEnd_5804606 : Nat := 4983230072969 + 3 ^ 40 * 5804606 * 2
def baseEnd_5804606 : Nat := 12265649744740829983663

theorem tailTrace_5804606 : CollatzResearch.WordTrace tailWord_5804606 prefixEnd_5804606 12265649744740829983663 := by
  unfold tailWord_5804606
  simp only [CollatzResearch.WordTrace]
  refine ⟨26463921701113910578085209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141140915739274189749787781 26463921701113910578085209)
  ·
    refine ⟨19847941275835432933563907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26463921701113910578085209 19847941275835432933563907)
    ·
      refine ⟨29771911913753149400345861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19847941275835432933563907 29771911913753149400345861)
      ·
        refine ⟨5582233483828715512564849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29771911913753149400345861 5582233483828715512564849)
        ·
          refine ⟨4186675112871536634423637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5582233483828715512564849 4186675112871536634423637)
          ·
            refine ⟨12265649744740829983663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4186675112871536634423637 12265649744740829983663)
            ·
              rfl

theorem cell23_5804606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 10].length) (baseStart_5804606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5804606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5804606 prefixEnd_5804606 := by exact prefixLift 5804606
  have htrace : WordTrace (prefixWord ++ tailWord_5804606) baseStart_5804606 baseEnd_5804606 := by
    simpa [prefixWord, tailWord_5804606, baseEnd_5804606] using wordTrace_append hprefix tailTrace_5804606
  have hstable : (prefixWord ++ tailWord_5804606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5804606).length < 2 ^ (prefixWord ++ tailWord_5804606).sum := by decide
  have hdescent : baseEnd_5804606 < baseStart_5804606 := by decide
  rcases family_descends (prefixWord ++ tailWord_5804606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5804626 : List Nat := [3, 2, 2, 1, 2, 1, 1, 1, 5, 3, 2]
def baseStart_5804626 : Nat := 118140960795 + 5804626 * 2 ^ 59
def prefixEnd_5804626 : Nat := 4983230072969 + 3 ^ 40 * 5804626 * 2
def baseEnd_5804626 : Nat := 2980563157585111607780017

theorem tailTrace_5804626 : CollatzResearch.WordTrace tailWord_5804626 prefixEnd_5804626 2980563157585111607780017 := by
  unfold tailWord_5804626
  simp only [CollatzResearch.WordTrace]
  refine ⟨52928025767209707010102433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141141402045892552026939821 52928025767209707010102433)
  ·
    refine ⟨39696019325407280257576825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52928025767209707010102433 39696019325407280257576825)
    ·
      refine ⟨29772014494055460193182619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39696019325407280257576825 29772014494055460193182619)
      ·
        refine ⟨44658021741083190289773929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29772014494055460193182619 44658021741083190289773929)
        ·
          refine ⟨33493516305812392717330447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44658021741083190289773929 33493516305812392717330447)
          ·
            refine ⟨50240274458718589075995671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33493516305812392717330447 50240274458718589075995671)
            ·
              refine ⟨75360411688077883613993507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50240274458718589075995671 75360411688077883613993507)
              ·
                refine ⟨113040617532116825420990261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75360411688077883613993507 113040617532116825420990261)
                ·
                  refine ⟨10597557893635952383217837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 113040617532116825420990261 10597557893635952383217837)
                  ·
                    refine ⟨3974084210113482143706689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10597557893635952383217837 3974084210113482143706689)
                    ·
                      refine ⟨2980563157585111607780017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3974084210113482143706689 2980563157585111607780017)
                      ·
                        rfl

theorem cell23_5804626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 5, 3, 2].length) (baseStart_5804626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5804626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5804626 prefixEnd_5804626 := by exact prefixLift 5804626
  have htrace : WordTrace (prefixWord ++ tailWord_5804626) baseStart_5804626 baseEnd_5804626 := by
    simpa [prefixWord, tailWord_5804626, baseEnd_5804626] using wordTrace_append hprefix tailTrace_5804626
  have hstable : (prefixWord ++ tailWord_5804626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5804626).length < 2 ^ (prefixWord ++ tailWord_5804626).sum := by decide
  have hdescent : baseEnd_5804626 < baseStart_5804626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5804626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5804632 : List Nat := [2, 1, 2, 2, 1, 2, 3, 1, 1, 8]
def baseStart_5804632 : Nat := 118140960795 + 5804632 * 2 ^ 59
def prefixEnd_5804632 : Nat := 4983230072969 + 3 ^ 40 * 5804632 * 2
def baseEnd_5804632 : Nat := 993522079489679528101663

theorem tailTrace_5804632 : CollatzResearch.WordTrace tailWord_5804632 prefixEnd_5804632 993522079489679528101663 := by
  unfold tailWord_5804632
  simp only [CollatzResearch.WordTrace]
  refine ⟨105856160953408545532564075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141141547937878060710085433 105856160953408545532564075)
  ·
    refine ⟨158784241430112818298846113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105856160953408545532564075 158784241430112818298846113)
    ·
      refine ⟨119088181072584613724134585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158784241430112818298846113 119088181072584613724134585)
      ·
        refine ⟨89316135804438460293100939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119088181072584613724134585 89316135804438460293100939)
        ·
          refine ⟨133974203706657690439651409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89316135804438460293100939 133974203706657690439651409)
          ·
            refine ⟨100480652779993267829738557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133974203706657690439651409 100480652779993267829738557)
            ·
              refine ⟨37680244792497475436151959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100480652779993267829738557 37680244792497475436151959)
              ·
                refine ⟨56520367188746213154227939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37680244792497475436151959 56520367188746213154227939)
                ·
                  refine ⟨84780550783119319731341909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56520367188746213154227939 84780550783119319731341909)
                  ·
                    refine ⟨993522079489679528101663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 84780550783119319731341909 993522079489679528101663)
                    ·
                      rfl

theorem cell23_5804632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 1, 8].length) (baseStart_5804632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5804632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5804632 prefixEnd_5804632 := by exact prefixLift 5804632
  have htrace : WordTrace (prefixWord ++ tailWord_5804632) baseStart_5804632 baseEnd_5804632 := by
    simpa [prefixWord, tailWord_5804632, baseEnd_5804632] using wordTrace_append hprefix tailTrace_5804632
  have hstable : (prefixWord ++ tailWord_5804632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5804632).length < 2 ^ (prefixWord ++ tailWord_5804632).sum := by decide
  have hdescent : baseEnd_5804632 < baseStart_5804632 := by decide
  rcases family_descends (prefixWord ++ tailWord_5804632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5804673 : List Nat := [1, 2, 4, 2, 1, 1, 3, 1, 4, 2, 2]
def baseStart_5804673 : Nat := 118140960795 + 5804673 * 2 ^ 59
def prefixEnd_5804673 : Nat := 4983230072969 + 3 ^ 40 * 5804673 * 2
def baseEnd_5804673 : Nat := 2980587291175872923892301

theorem tailTrace_5804673 : CollatzResearch.WordTrace tailWord_5804673 prefixEnd_5804673 2980587291175872923892301 := by
  unfold tailWord_5804673
  simp only [CollatzResearch.WordTrace]
  refine ⟨211713817299668555067370673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141142544866445703378247115 211713817299668555067370673)
  ·
    refine ⟨158785362974751416300528005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211713817299668555067370673 158785362974751416300528005)
    ·
      refine ⟨29772255557765890556349001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158785362974751416300528005 29772255557765890556349001)
      ·
        refine ⟨22329191668324417917261751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29772255557765890556349001 22329191668324417917261751)
        ·
          refine ⟨33493787502486626875892627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22329191668324417917261751 33493787502486626875892627)
          ·
            refine ⟨50240681253729940313838941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33493787502486626875892627 50240681253729940313838941)
            ·
              refine ⟨18840255470148727617689603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50240681253729940313838941 18840255470148727617689603)
              ·
                refine ⟨28260383205223091426534405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18840255470148727617689603 28260383205223091426534405)
                ·
                  refine ⟨5298821850979329642475201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28260383205223091426534405 5298821850979329642475201)
                  ·
                    refine ⟨3974116388234497231856401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5298821850979329642475201 3974116388234497231856401)
                    ·
                      refine ⟨2980587291175872923892301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3974116388234497231856401 2980587291175872923892301)
                      ·
                        rfl

theorem cell23_5804673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_5804673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5804673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5804673 prefixEnd_5804673 := by exact prefixLift 5804673
  have htrace : WordTrace (prefixWord ++ tailWord_5804673) baseStart_5804673 baseEnd_5804673 := by
    simpa [prefixWord, tailWord_5804673, baseEnd_5804673] using wordTrace_append hprefix tailTrace_5804673
  have hstable : (prefixWord ++ tailWord_5804673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5804673).length < 2 ^ (prefixWord ++ tailWord_5804673).sum := by decide
  have hdescent : baseEnd_5804673 < baseStart_5804673 := by decide
  rcases family_descends (prefixWord ++ tailWord_5804673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5804679 : List Nat := [1, 1, 4, 2, 1, 2, 4, 1, 7]
def baseStart_5804679 : Nat := 118140960795 + 5804679 * 2 ^ 59
def prefixEnd_5804679 : Nat := 4983230072969 + 3 ^ 40 * 5804679 * 2
def baseEnd_5804679 : Nat := 331176708006644433379697

theorem tailTrace_5804679 : CollatzResearch.WordTrace tailWord_5804679 prefixEnd_5804679 331176708006644433379697 := by
  unfold tailWord_5804679
  simp only [CollatzResearch.WordTrace]
  refine ⟨211714036137646818092089091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141142690758431212061392727 211714036137646818092089091)
  ·
    refine ⟨317571054206470227138133637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211714036137646818092089091 317571054206470227138133637)
    ·
      refine ⟨59544572663713167588400057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 317571054206470227138133637 59544572663713167588400057)
      ·
        refine ⟨44658429497784875691300043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59544572663713167588400057 44658429497784875691300043)
        ·
          refine ⟨66987644246677313536950065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44658429497784875691300043 66987644246677313536950065)
          ·
            refine ⟨50240733185007985152712549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66987644246677313536950065 50240733185007985152712549)
            ·
              refine ⟨9420137472188997216133603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50240733185007985152712549 9420137472188997216133603)
              ·
                refine ⟨14130206208283495824200405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9420137472188997216133603 14130206208283495824200405)
                ·
                  refine ⟨331176708006644433379697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14130206208283495824200405 331176708006644433379697)
                  ·
                    rfl

theorem cell23_5804679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 7].length) (baseStart_5804679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5804679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5804679 prefixEnd_5804679 := by exact prefixLift 5804679
  have htrace : WordTrace (prefixWord ++ tailWord_5804679) baseStart_5804679 baseEnd_5804679 := by
    simpa [prefixWord, tailWord_5804679, baseEnd_5804679] using wordTrace_append hprefix tailTrace_5804679
  have hstable : (prefixWord ++ tailWord_5804679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5804679).length < 2 ^ (prefixWord ++ tailWord_5804679).sum := by decide
  have hdescent : baseEnd_5804679 < baseStart_5804679 := by decide
  rcases family_descends (prefixWord ++ tailWord_5804679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5804690 : List Nat := [3, 2, 3, 1, 2, 3, 1, 1, 1, 4, 2]
def baseStart_5804690 : Nat := 118140960795 + 5804690 * 2 ^ 59
def prefixEnd_5804690 : Nat := 4983230072969 + 3 ^ 40 * 5804690 * 2
def baseEnd_5804690 : Nat := 2980596020346999357379723

theorem tailTrace_5804690 : CollatzResearch.WordTrace tailWord_5804690 prefixEnd_5804690 2980596020346999357379723 := by
  unfold tailWord_5804690
  simp only [CollatzResearch.WordTrace]
  refine ⟨52928609335151741742684881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141142958227071311313826349 52928609335151741742684881)
  ·
    refine ⟨39696457001363806307013661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52928609335151741742684881 39696457001363806307013661)
    ·
      refine ⟨14886171375511427365130123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39696457001363806307013661 14886171375511427365130123)
      ·
        refine ⟨22329257063267141047695185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14886171375511427365130123 22329257063267141047695185)
        ·
          refine ⟨16746942797450355785771389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22329257063267141047695185 16746942797450355785771389)
          ·
            refine ⟨6280103549043883419664271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16746942797450355785771389 6280103549043883419664271)
            ·
              refine ⟨9420155323565825129496407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6280103549043883419664271 9420155323565825129496407)
              ·
                refine ⟨14130232985348737694244611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9420155323565825129496407 14130232985348737694244611)
                ·
                  refine ⟨21195349478023106541366917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14130232985348737694244611 21195349478023106541366917)
                  ·
                    refine ⟨3974128027129332476506297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21195349478023106541366917 3974128027129332476506297)
                    ·
                      refine ⟨2980596020346999357379723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3974128027129332476506297 2980596020346999357379723)
                      ·
                        rfl

theorem cell23_5804690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_5804690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5804690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5804690 prefixEnd_5804690 := by exact prefixLift 5804690
  have htrace : WordTrace (prefixWord ++ tailWord_5804690) baseStart_5804690 baseEnd_5804690 := by
    simpa [prefixWord, tailWord_5804690, baseEnd_5804690] using wordTrace_append hprefix tailTrace_5804690
  have hstable : (prefixWord ++ tailWord_5804690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5804690).length < 2 ^ (prefixWord ++ tailWord_5804690).sum := by decide
  have hdescent : baseEnd_5804690 < baseStart_5804690 := by decide
  rcases family_descends (prefixWord ++ tailWord_5804690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5804709 : List Nat := [1, 3, 1, 2, 1, 2, 1, 5, 2, 5]
def baseStart_5804709 : Nat := 118140960795 + 5804709 * 2 ^ 59
def prefixEnd_5804709 : Nat := 4983230072969 + 3 ^ 40 * 5804709 * 2
def baseEnd_5804709 : Nat := 993535258826478261014045

theorem tailTrace_5804709 : CollatzResearch.WordTrace tailWord_5804709 prefixEnd_5804709 993535258826478261014045 := by
  unfold tailWord_5804709
  simp only [CollatzResearch.WordTrace]
  refine ⟨211715130327538133215681181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141143420218358755477120787 211715130327538133215681181)
  ·
    refine ⟨79393173872826799955880443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211715130327538133215681181 79393173872826799955880443)
    ·
      refine ⟨119089760809240199933820665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79393173872826799955880443 119089760809240199933820665)
      ·
        refine ⟨89317320606930149950365499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119089760809240199933820665 89317320606930149950365499)
        ·
          refine ⟨133975980910395224925548249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89317320606930149950365499 133975980910395224925548249)
          ·
            refine ⟨100481985682796418694161187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133975980910395224925548249 100481985682796418694161187)
            ·
              refine ⟨150722978524194628041241781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100481985682796418694161187 150722978524194628041241781)
              ·
                refine ⟨14130279236643246378866417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 150722978524194628041241781 14130279236643246378866417)
                ·
                  refine ⟨10597709427482434784149813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14130279236643246378866417 10597709427482434784149813)
                  ·
                    refine ⟨993535258826478261014045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10597709427482434784149813 993535258826478261014045)
                    ·
                      rfl

theorem cell23_5804709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 2, 5].length) (baseStart_5804709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5804709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5804709 prefixEnd_5804709 := by exact prefixLift 5804709
  have htrace : WordTrace (prefixWord ++ tailWord_5804709) baseStart_5804709 baseEnd_5804709 := by
    simpa [prefixWord, tailWord_5804709, baseEnd_5804709] using wordTrace_append hprefix tailTrace_5804709
  have hstable : (prefixWord ++ tailWord_5804709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5804709).length < 2 ^ (prefixWord ++ tailWord_5804709).sum := by decide
  have hdescent : baseEnd_5804709 < baseStart_5804709 := by decide
  rcases family_descends (prefixWord ++ tailWord_5804709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5804786 : List Nat := [3, 2, 1, 3, 1, 2, 1, 4, 6]
def baseStart_5804786 : Nat := 118140960795 + 5804786 * 2 ^ 59
def prefixEnd_5804786 : Nat := 4983230072969 + 3 ^ 40 * 5804786 * 2
def baseEnd_5804786 : Nat := 331182812721092331308809

theorem tailTrace_5804786 : CollatzResearch.WordTrace tailWord_5804786 prefixEnd_5804786 331182812721092331308809 := by
  unfold tailWord_5804786
  simp only [CollatzResearch.WordTrace]
  refine ⟨52929484687064793841558553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141145292498839450244156141 52929484687064793841558553)
  ·
    refine ⟨39697113515298595381168915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52929484687064793841558553 39697113515298595381168915)
    ·
      refine ⟨59545670272947893071753373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39697113515298595381168915 59545670272947893071753373)
      ·
        refine ⟨22329626352355459901907515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59545670272947893071753373 22329626352355459901907515)
        ·
          refine ⟨33494439528533189852861273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22329626352355459901907515 33494439528533189852861273)
          ·
            refine ⟨25120829646399892389645955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33494439528533189852861273 25120829646399892389645955)
            ·
              refine ⟨37681244469599838584468933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25120829646399892389645955 37681244469599838584468933)
              ·
                refine ⟨7065233338049969734587925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37681244469599838584468933 7065233338049969734587925)
                ·
                  refine ⟨331182812721092331308809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7065233338049969734587925 331182812721092331308809)
                  ·
                    rfl

theorem cell23_5804786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 4, 6].length) (baseStart_5804786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5804786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5804786 prefixEnd_5804786 := by exact prefixLift 5804786
  have htrace : WordTrace (prefixWord ++ tailWord_5804786) baseStart_5804786 baseEnd_5804786 := by
    simpa [prefixWord, tailWord_5804786, baseEnd_5804786] using wordTrace_append hprefix tailTrace_5804786
  have hstable : (prefixWord ++ tailWord_5804786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5804786).length < 2 ^ (prefixWord ++ tailWord_5804786).sum := by decide
  have hdescent : baseEnd_5804786 < baseStart_5804786 := by decide
  rcases family_descends (prefixWord ++ tailWord_5804786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5804790 : List Nat := [5, 1, 1, 1, 1, 2, 3, 4, 1, 4]
def baseStart_5804790 : Nat := 118140960795 + 5804790 * 2 ^ 59
def prefixEnd_5804790 : Nat := 4983230072969 + 3 ^ 40 * 5804790 * 2
def baseEnd_5804790 : Nat := 993549122804149655376421

theorem tailTrace_5804790 : CollatzResearch.WordTrace tailWord_5804790 prefixEnd_5804790 993549122804149655376421 := by
  unfold tailWord_5804790
  simp only [CollatzResearch.WordTrace]
  refine ⟨13232380290015292753086239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141145389760163122699586549 13232380290015292753086239)
  ·
    refine ⟨19848570435022939129629359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13232380290015292753086239 19848570435022939129629359)
    ·
      refine ⟨29772855652534408694444039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19848570435022939129629359 29772855652534408694444039)
      ·
        refine ⟨44659283478801613041666059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29772855652534408694444039 44659283478801613041666059)
        ·
          refine ⟨66988925218202419562499089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44659283478801613041666059 66988925218202419562499089)
          ·
            refine ⟨50241693913651814671874317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66988925218202419562499089 50241693913651814671874317)
            ·
              refine ⟨18840635217619430501952869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50241693913651814671874317 18840635217619430501952869)
              ·
                refine ⟨3532619103303643219116163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18840635217619430501952869 3532619103303643219116163)
                ·
                  refine ⟨5298928654955464828674245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3532619103303643219116163 5298928654955464828674245)
                  ·
                    refine ⟨993549122804149655376421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5298928654955464828674245 993549122804149655376421)
                    ·
                      rfl

theorem cell23_5804790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_5804790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5804790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5804790 prefixEnd_5804790 := by exact prefixLift 5804790
  have htrace : WordTrace (prefixWord ++ tailWord_5804790) baseStart_5804790 baseEnd_5804790 := by
    simpa [prefixWord, tailWord_5804790, baseEnd_5804790] using wordTrace_append hprefix tailTrace_5804790
  have hstable : (prefixWord ++ tailWord_5804790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5804790).length < 2 ^ (prefixWord ++ tailWord_5804790).sum := by decide
  have hdescent : baseEnd_5804790 < baseStart_5804790 := by decide
  rcases family_descends (prefixWord ++ tailWord_5804790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5804856 : List Nat := [2, 1, 2, 1, 3, 2, 3, 2, 1, 1, 5]
def baseStart_5804856 : Nat := 118140960795 + 5804856 * 2 ^ 59
def prefixEnd_5804856 : Nat := 4983230072969 + 3 ^ 40 * 5804856 * 2
def baseEnd_5804856 : Nat := 2980681258135645707903959

theorem tailTrace_5804856 : CollatzResearch.WordTrace tailWord_5804856 prefixEnd_5804856 2980681258135645707903959 := by
  unfold tailWord_5804856
  simp only [CollatzResearch.WordTrace]
  refine ⟨105860245929002788660641211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141146994572003718214188281 105860245929002788660641211)
  ·
    refine ⟨158790368893504182990961817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105860245929002788660641211 158790368893504182990961817)
    ·
      refine ⟨119092776670128137243221363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158790368893504182990961817 119092776670128137243221363)
      ·
        refine ⟨178639165005192205864832045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119092776670128137243221363 178639165005192205864832045)
        ·
          refine ⟨66989686876947077199312017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178639165005192205864832045 66989686876947077199312017)
          ·
            refine ⟨50242265157710307899484013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66989686876947077199312017 50242265157710307899484013)
            ·
              refine ⟨18840849434141365462306505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50242265157710307899484013 18840849434141365462306505)
              ·
                refine ⟨14130637075606024096729879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18840849434141365462306505 14130637075606024096729879)
                ·
                  refine ⟨21195955613409036145094819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14130637075606024096729879 21195955613409036145094819)
                  ·
                    refine ⟨31793933420113554217642229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21195955613409036145094819 31793933420113554217642229)
                    ·
                      refine ⟨2980681258135645707903959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31793933420113554217642229 2980681258135645707903959)
                      ·
                        rfl

theorem cell23_5804856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 1, 1, 5].length) (baseStart_5804856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5804856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5804856 prefixEnd_5804856 := by exact prefixLift 5804856
  have htrace : WordTrace (prefixWord ++ tailWord_5804856) baseStart_5804856 baseEnd_5804856 := by
    simpa [prefixWord, tailWord_5804856, baseEnd_5804856] using wordTrace_append hprefix tailTrace_5804856
  have hstable : (prefixWord ++ tailWord_5804856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5804856).length < 2 ^ (prefixWord ++ tailWord_5804856).sum := by decide
  have hdescent : baseEnd_5804856 < baseStart_5804856 := by decide
  rcases family_descends (prefixWord ++ tailWord_5804856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5804863 : List Nat := [1, 1, 2, 2, 5, 3, 1, 1, 1, 6]
def baseStart_5804863 : Nat := 118140960795 + 5804863 * 2 ^ 59
def prefixEnd_5804863 : Nat := 4983230072969 + 3 ^ 40 * 5804863 * 2
def baseEnd_5804863 : Nat := 993561617500075726838809

theorem tailTrace_5804863 : CollatzResearch.WordTrace tailWord_5804863 prefixEnd_5804863 993561617500075726838809 := by
  unfold tailWord_5804863
  simp only [CollatzResearch.WordTrace]
  refine ⟨211720747168980217516787243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141147164779320145011191495 211720747168980217516787243)
  ·
    refine ⟨317581120753470326275180865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211720747168980217516787243 317581120753470326275180865)
    ·
      refine ⟨238185840565102744706385649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317581120753470326275180865 238185840565102744706385649)
      ·
        refine ⟨178639380423827058529789237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238185840565102744706385649 178639380423827058529789237)
        ·
          refine ⟨16747441914733786737167741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 178639380423827058529789237 16747441914733786737167741)
          ·
            refine ⟨6280290718025170026437903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16747441914733786737167741 6280290718025170026437903)
            ·
              refine ⟨9420436077037755039656855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6280290718025170026437903 9420436077037755039656855)
              ·
                refine ⟨14130654115556632559485283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9420436077037755039656855 14130654115556632559485283)
                ·
                  refine ⟨21195981173334948839227925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14130654115556632559485283 21195981173334948839227925)
                  ·
                    refine ⟨993561617500075726838809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21195981173334948839227925 993561617500075726838809)
                    ·
                      rfl

theorem cell23_5804863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 6].length) (baseStart_5804863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5804863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5804863 prefixEnd_5804863 := by exact prefixLift 5804863
  have htrace : WordTrace (prefixWord ++ tailWord_5804863) baseStart_5804863 baseEnd_5804863 := by
    simpa [prefixWord, tailWord_5804863, baseEnd_5804863] using wordTrace_append hprefix tailTrace_5804863
  have hstable : (prefixWord ++ tailWord_5804863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5804863).length < 2 ^ (prefixWord ++ tailWord_5804863).sum := by decide
  have hdescent : baseEnd_5804863 < baseStart_5804863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5804863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5804873 : List Nat := [1, 2, 1, 1, 2, 5, 1, 4, 1, 2, 3]
def baseStart_5804873 : Nat := 118140960795 + 5804873 * 2 ^ 59
def prefixEnd_5804873 : Nat := 4983230072969 + 3 ^ 40 * 5804873 * 2
def baseEnd_5804873 : Nat := 2980689987306772141391381

theorem tailTrace_5804873 : CollatzResearch.WordTrace tailWord_5804873 prefixEnd_5804873 2980689987306772141391381 := by
  unfold tailWord_5804873
  simp only [CollatzResearch.WordTrace]
  refine ⟨211721111898943989224651273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141147407932629326149767515 211721111898943989224651273)
  ·
    refine ⟨158790833924207991918488455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211721111898943989224651273 158790833924207991918488455)
    ·
      refine ⟨238186250886311987877732683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158790833924207991918488455 238186250886311987877732683)
      ·
        refine ⟨357279376329467981816599025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238186250886311987877732683 357279376329467981816599025)
        ·
          refine ⟨267959532247100986362449269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 357279376329467981816599025 267959532247100986362449269)
          ·
            refine ⟨25121206148165717471479619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 267959532247100986362449269 25121206148165717471479619)
            ·
              refine ⟨37681809222248576207219429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25121206148165717471479619 37681809222248576207219429)
              ·
                refine ⟨7065339229171608038853643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37681809222248576207219429 7065339229171608038853643)
                ·
                  refine ⟨10598008843757412058280465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7065339229171608038853643 10598008843757412058280465)
                  ·
                    refine ⟨7948506632818059043710349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10598008843757412058280465 7948506632818059043710349)
                    ·
                      refine ⟨2980689987306772141391381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7948506632818059043710349 2980689987306772141391381)
                      ·
                        rfl

theorem cell23_5804873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 4, 1, 2, 3].length) (baseStart_5804873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5804873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5804873 prefixEnd_5804873 := by exact prefixLift 5804873
  have htrace : WordTrace (prefixWord ++ tailWord_5804873) baseStart_5804873 baseEnd_5804873 := by
    simpa [prefixWord, tailWord_5804873, baseEnd_5804873] using wordTrace_append hprefix tailTrace_5804873
  have hstable : (prefixWord ++ tailWord_5804873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5804873).length < 2 ^ (prefixWord ++ tailWord_5804873).sum := by decide
  have hdescent : baseEnd_5804873 < baseStart_5804873 := by decide
  rcases family_descends (prefixWord ++ tailWord_5804873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5804876 : List Nat := [2, 2, 1, 3, 3, 2, 1, 9]
def baseStart_5804876 : Nat := 118140960795 + 5804876 * 2 ^ 59
def prefixEnd_5804876 : Nat := 4983230072969 + 3 ^ 40 * 5804876 * 2
def baseEnd_5804876 : Nat := 110395982509212430727921

theorem tailTrace_5804876 : CollatzResearch.WordTrace tailWord_5804876 prefixEnd_5804876 110395982509212430727921 := by
  unfold tailWord_5804876
  simp only [CollatzResearch.WordTrace]
  refine ⟨105860610658966560368505241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141147480878622080491340321 105860610658966560368505241)
  ·
    refine ⟨79395457994224920276378931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105860610658966560368505241 79395457994224920276378931)
    ·
      refine ⟨119093186991337380414568397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79395457994224920276378931 119093186991337380414568397)
      ·
        refine ⟨44659945121751517655463149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119093186991337380414568397 44659945121751517655463149)
        ·
          refine ⟨16747479420656819120798681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44659945121751517655463149 16747479420656819120798681)
          ·
            refine ⟨12560609565492614340599011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16747479420656819120798681 12560609565492614340599011)
            ·
              refine ⟨18840914348238921510898517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12560609565492614340599011 18840914348238921510898517)
              ·
                refine ⟨110395982509212430727921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18840914348238921510898517 110395982509212430727921)
                ·
                  rfl

theorem cell23_5804876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 9].length) (baseStart_5804876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5804876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5804876 prefixEnd_5804876 := by exact prefixLift 5804876
  have htrace : WordTrace (prefixWord ++ tailWord_5804876) baseStart_5804876 baseEnd_5804876 := by
    simpa [prefixWord, tailWord_5804876, baseEnd_5804876] using wordTrace_append hprefix tailTrace_5804876
  have hstable : (prefixWord ++ tailWord_5804876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5804876).length < 2 ^ (prefixWord ++ tailWord_5804876).sum := by decide
  have hdescent : baseEnd_5804876 < baseStart_5804876 := by decide
  rcases family_descends (prefixWord ++ tailWord_5804876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5804879 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 6]
def baseStart_5804879 : Nat := 118140960795 + 5804879 * 2 ^ 59
def prefixEnd_5804879 : Nat := 4983230072969 + 3 ^ 40 * 5804879 * 2
def baseEnd_5804879 : Nat := 2980693068190699117916353

theorem tailTrace_5804879 : CollatzResearch.WordTrace tailWord_5804879 prefixEnd_5804879 2980693068190699117916353 := by
  unfold tailWord_5804879
  simp only [CollatzResearch.WordTrace]
  refine ⟨211721330736922252249369691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141147553824614834832913127 211721330736922252249369691)
  ·
    refine ⟨317581996105383378374054537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211721330736922252249369691 317581996105383378374054537)
    ·
      refine ⟨238186497079037533780540903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317581996105383378374054537 238186497079037533780540903)
      ·
        refine ⟨357279745618556300670811355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238186497079037533780540903 357279745618556300670811355)
        ·
          refine ⟨535919618427834451006217033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357279745618556300670811355 535919618427834451006217033)
          ·
            refine ⟨401939713820875838254662775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 535919618427834451006217033 401939713820875838254662775)
            ·
              refine ⟨602909570731313757381994163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 401939713820875838254662775 602909570731313757381994163)
              ·
                refine ⟨904364356096970636072991245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 602909570731313757381994163 904364356096970636072991245)
                ·
                  refine ⟨339136633536363988527371717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 904364356096970636072991245 339136633536363988527371717)
                  ·
                    refine ⟨63588118788068247848882197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 339136633536363988527371717 63588118788068247848882197)
                    ·
                      refine ⟨2980693068190699117916353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63588118788068247848882197 2980693068190699117916353)
                      ·
                        rfl

theorem cell23_5804879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 6].length) (baseStart_5804879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5804879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5804879 prefixEnd_5804879 := by exact prefixLift 5804879
  have htrace : WordTrace (prefixWord ++ tailWord_5804879) baseStart_5804879 baseEnd_5804879 := by
    simpa [prefixWord, tailWord_5804879, baseEnd_5804879] using wordTrace_append hprefix tailTrace_5804879
  have hstable : (prefixWord ++ tailWord_5804879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5804879).length < 2 ^ (prefixWord ++ tailWord_5804879).sum := by decide
  have hdescent : baseEnd_5804879 < baseStart_5804879 := by decide
  rcases family_descends (prefixWord ++ tailWord_5804879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5804960 : List Nat := [2, 1, 1, 4, 1, 1, 2, 3, 4, 2, 2]
def baseStart_5804960 : Nat := 118140960795 + 5804960 * 2 ^ 59
def prefixEnd_5804960 : Nat := 4983230072969 + 3 ^ 40 * 5804960 * 2
def baseEnd_5804960 : Nat := 2980734660123713301003481

theorem tailTrace_5804960 : CollatzResearch.WordTrace tailWord_5804960 prefixEnd_5804960 2980734660123713301003481 := by
  unfold tailWord_5804960
  simp only [CollatzResearch.WordTrace]
  refine ⟨105862142524814401541534167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141149523366419202055378889 105862142524814401541534167)
  ·
    refine ⟨158793213787221602312301251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105862142524814401541534167 158793213787221602312301251)
    ·
      refine ⟨238189820680832403468451877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158793213787221602312301251 238189820680832403468451877)
      ·
        refine ⟨44660591377656075650334727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 238189820680832403468451877 44660591377656075650334727)
        ·
          refine ⟨66990887066484113475502091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44660591377656075650334727 66990887066484113475502091)
          ·
            refine ⟨100486330599726170213253137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66990887066484113475502091 100486330599726170213253137)
            ·
              refine ⟨75364747949794627659939853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100486330599726170213253137 75364747949794627659939853)
              ·
                refine ⟨28261780481172985372477445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75364747949794627659939853 28261780481172985372477445)
                ·
                  refine ⟨5299083840219934757339521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28261780481172985372477445 5299083840219934757339521)
                  ·
                    refine ⟨3974312880164951068004641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5299083840219934757339521 3974312880164951068004641)
                    ·
                      refine ⟨2980734660123713301003481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3974312880164951068004641 2980734660123713301003481)
                      ·
                        rfl

theorem cell23_5804960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 4, 2, 2].length) (baseStart_5804960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5804960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5804960 prefixEnd_5804960 := by exact prefixLift 5804960
  have htrace : WordTrace (prefixWord ++ tailWord_5804960) baseStart_5804960 baseEnd_5804960 := by
    simpa [prefixWord, tailWord_5804960, baseEnd_5804960] using wordTrace_append hprefix tailTrace_5804960
  have hstable : (prefixWord ++ tailWord_5804960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5804960).length < 2 ^ (prefixWord ++ tailWord_5804960).sum := by decide
  have hdescent : baseEnd_5804960 < baseStart_5804960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5804960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5804977 : List Nat := [1, 2, 2, 4, 3, 1, 2, 1, 1, 4, 2]
def baseStart_5804977 : Nat := 118140960795 + 5804977 * 2 ^ 59
def prefixEnd_5804977 : Nat := 4983230072969 + 3 ^ 40 * 5804977 * 2
def baseEnd_5804977 : Nat := 2980743389294839734490903

theorem tailTrace_5804977 : CollatzResearch.WordTrace tailWord_5804977 prefixEnd_5804977 2980743389294839734490903 := by
  unfold tailWord_5804977
  simp only [CollatzResearch.WordTrace]
  refine ⟨211724905090567214986437185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141149936727044809990958123 211724905090567214986437185)
  ·
    refine ⟨158793678817925411239827889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211724905090567214986437185 158793678817925411239827889)
    ·
      refine ⟨119095259113444058429870917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158793678817925411239827889 119095259113444058429870917)
      ·
        refine ⟨22330361083770760955600797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119095259113444058429870917 22330361083770760955600797)
        ·
          refine ⟨8373885406414035358350299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22330361083770760955600797 8373885406414035358350299)
          ·
            refine ⟨12560828109621053037525449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8373885406414035358350299 12560828109621053037525449)
            ·
              refine ⟨9420621082215789778144087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12560828109621053037525449 9420621082215789778144087)
              ·
                refine ⟨14130931623323684667216131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9420621082215789778144087 14130931623323684667216131)
                ·
                  refine ⟨21196397434985527000824197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14130931623323684667216131 21196397434985527000824197)
                  ·
                    refine ⟨3974324519059786312654537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21196397434985527000824197 3974324519059786312654537)
                    ·
                      refine ⟨2980743389294839734490903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3974324519059786312654537 2980743389294839734490903)
                      ·
                        rfl

theorem cell23_5804977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_5804977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5804977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5804977 prefixEnd_5804977 := by exact prefixLift 5804977
  have htrace : WordTrace (prefixWord ++ tailWord_5804977) baseStart_5804977 baseEnd_5804977 := by
    simpa [prefixWord, tailWord_5804977, baseEnd_5804977] using wordTrace_append hprefix tailTrace_5804977
  have hstable : (prefixWord ++ tailWord_5804977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5804977).length < 2 ^ (prefixWord ++ tailWord_5804977).sum := by decide
  have hdescent : baseEnd_5804977 < baseStart_5804977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5804977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805005 : List Nat := [1, 6, 3, 1, 2, 1, 1, 2, 2, 1, 3]
def baseStart_5805005 : Nat := 118140960795 + 5805005 * 2 ^ 59
def prefixEnd_5805005 : Nat := 4983230072969 + 3 ^ 40 * 5805005 * 2
def baseEnd_5805005 : Nat := 2980757766753165624940775

theorem tailTrace_5805005 : CollatzResearch.WordTrace tailWord_5805005 prefixEnd_5805005 2980757766753165624940775 := by
  unfold tailWord_5805005
  simp only [CollatzResearch.WordTrace]
  refine ⟨211725926334465775768456469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141150617556310517178970979 211725926334465775768456469)
  ·
    refine ⟨9924652796928083239146397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 211725926334465775768456469 9924652796928083239146397)
    ·
      refine ⟨3721744798848031214679899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9924652796928083239146397 3721744798848031214679899)
      ·
        refine ⟨5582617198272046822019849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3721744798848031214679899 5582617198272046822019849)
        ·
          refine ⟨4186962898704035116514887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5582617198272046822019849 4186962898704035116514887)
          ·
            refine ⟨6280444348056052674772331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4186962898704035116514887 6280444348056052674772331)
            ·
              refine ⟨9420666522084079012158497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6280444348056052674772331 9420666522084079012158497)
              ·
                refine ⟨7065499891563059259118873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9420666522084079012158497 7065499891563059259118873)
                ·
                  refine ⟨5299124918672294444339155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7065499891563059259118873 5299124918672294444339155)
                  ·
                    refine ⟨7948687378008441666508733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5299124918672294444339155 7948687378008441666508733)
                    ·
                      refine ⟨2980757766753165624940775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7948687378008441666508733 2980757766753165624940775)
                      ·
                        rfl

theorem cell23_5805005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_5805005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805005 prefixEnd_5805005 := by exact prefixLift 5805005
  have htrace : WordTrace (prefixWord ++ tailWord_5805005) baseStart_5805005 baseEnd_5805005 := by
    simpa [prefixWord, tailWord_5805005, baseEnd_5805005] using wordTrace_append hprefix tailTrace_5805005
  have hstable : (prefixWord ++ tailWord_5805005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805005).length < 2 ^ (prefixWord ++ tailWord_5805005).sum := by decide
  have hdescent : baseEnd_5805005 < baseStart_5805005 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805010 : List Nat := [3, 2, 2, 3, 1, 1, 1, 2, 2, 3, 3]
def baseStart_5805010 : Nat := 118140960795 + 5805010 * 2 ^ 59
def prefixEnd_5805010 : Nat := 4983230072969 + 3 ^ 40 * 5805010 * 2
def baseEnd_5805010 : Nat := 2980760334156438105378251

theorem tailTrace_5805010 : CollatzResearch.WordTrace tailWord_5805010 prefixEnd_5805010 2980760334156438105378251 := by
  unfold tailWord_5805010
  simp only [CollatzResearch.WordTrace]
  refine ⟨52931527174861915405597121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141150739132965107748258989 52931527174861915405597121)
  ·
    refine ⟨39698645381146436554197841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52931527174861915405597121 39698645381146436554197841)
    ·
      refine ⟨29773984035859827415648381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39698645381146436554197841 29773984035859827415648381)
      ·
        refine ⟨11165244013447435280868143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29773984035859827415648381 11165244013447435280868143)
        ·
          refine ⟨16747866020171152921302215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11165244013447435280868143 16747866020171152921302215)
          ·
            refine ⟨25121799030256729381953323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16747866020171152921302215 25121799030256729381953323)
            ·
              refine ⟨37682698545385094072929985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25121799030256729381953323 37682698545385094072929985)
              ·
                refine ⟨28262023909038820554697489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37682698545385094072929985 28262023909038820554697489)
                ·
                  refine ⟨21196517931779115416023117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28262023909038820554697489 21196517931779115416023117)
                  ·
                    refine ⟨7948694224417168281008669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21196517931779115416023117 7948694224417168281008669)
                    ·
                      refine ⟨2980760334156438105378251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7948694224417168281008669 2980760334156438105378251)
                      ·
                        rfl

theorem cell23_5805010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_5805010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805010 prefixEnd_5805010 := by exact prefixLift 5805010
  have htrace : WordTrace (prefixWord ++ tailWord_5805010) baseStart_5805010 baseEnd_5805010 := by
    simpa [prefixWord, tailWord_5805010, baseEnd_5805010] using wordTrace_append hprefix tailTrace_5805010
  have hstable : (prefixWord ++ tailWord_5805010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805010).length < 2 ^ (prefixWord ++ tailWord_5805010).sum := by decide
  have hdescent : baseEnd_5805010 < baseStart_5805010 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805070 : List Nat := [4, 1, 1, 2, 2, 2, 1, 1, 4, 2, 3]
def baseStart_5805070 : Nat := 118140960795 + 5805070 * 2 ^ 59
def prefixEnd_5805070 : Nat := 4983230072969 + 3 ^ 40 * 5805070 * 2
def baseEnd_5805070 : Nat := 2980791142995707870627975

theorem tailTrace_5805070 : CollatzResearch.WordTrace tailWord_5805070 prefixEnd_5805070 2980791142995707870627975 := by
  unfold tailWord_5805070
  simp only [CollatzResearch.WordTrace]
  refine ⟨26466037134903786483696583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141152198052820194579715109 26466037134903786483696583)
  ·
    refine ⟨39699055702355679725544875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26466037134903786483696583 39699055702355679725544875)
    ·
      refine ⟨59548583553533519588317313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39699055702355679725544875 59548583553533519588317313)
      ·
        refine ⟨44661437665150139691237985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59548583553533519588317313 44661437665150139691237985)
        ·
          refine ⟨33496078248862604768428489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44661437665150139691237985 33496078248862604768428489)
          ·
            refine ⟨25122058686646953576321367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33496078248862604768428489 25122058686646953576321367)
            ·
              refine ⟨37683088029970430364482051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25122058686646953576321367 37683088029970430364482051)
              ·
                refine ⟨56524632044955645546723077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37683088029970430364482051 56524632044955645546723077)
                ·
                  refine ⟨10598368508429183540010577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56524632044955645546723077 10598368508429183540010577)
                  ·
                    refine ⟨7948776381321887655007933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10598368508429183540010577 7948776381321887655007933)
                    ·
                      refine ⟨2980791142995707870627975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7948776381321887655007933 2980791142995707870627975)
                      ·
                        rfl

theorem cell23_5805070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_5805070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805070 prefixEnd_5805070 := by exact prefixLift 5805070
  have htrace : WordTrace (prefixWord ++ tailWord_5805070) baseStart_5805070 baseEnd_5805070 := by
    simpa [prefixWord, tailWord_5805070, baseEnd_5805070] using wordTrace_append hprefix tailTrace_5805070
  have hstable : (prefixWord ++ tailWord_5805070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805070).length < 2 ^ (prefixWord ++ tailWord_5805070).sum := by decide
  have hdescent : baseEnd_5805070 < baseStart_5805070 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805074 : List Nat := [3, 2, 5, 1, 1, 1, 1, 1, 1, 2, 5]
def baseStart_5805074 : Nat := 118140960795 + 5805074 * 2 ^ 59
def prefixEnd_5805074 : Nat := 4983230072969 + 3 ^ 40 * 5805074 * 2
def baseEnd_5805074 : Nat := 2980793196918325854977957

theorem tailTrace_5805074 : CollatzResearch.WordTrace tailWord_5805074 prefixEnd_5805074 2980793196918325854977957 := by
  unfold tailWord_5805074
  simp only [CollatzResearch.WordTrace]
  refine ⟨52932110742803950138179569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141152295314143867035145517 52932110742803950138179569)
  ·
    refine ⟨39699083057102962603634677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52932110742803950138179569 39699083057102962603634677)
    ·
      refine ⟨3721789036603402744090751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39699083057102962603634677 3721789036603402744090751)
      ·
        refine ⟨5582683554905104116136127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3721789036603402744090751 5582683554905104116136127)
        ·
          refine ⟨8374025332357656174204191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5582683554905104116136127 8374025332357656174204191)
          ·
            refine ⟨12561037998536484261306287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8374025332357656174204191 12561037998536484261306287)
            ·
              refine ⟨18841556997804726391959431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12561037998536484261306287 18841556997804726391959431)
              ·
                refine ⟨28262335496707089587939147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18841556997804726391959431 28262335496707089587939147)
                ·
                  refine ⟨42393503245060634381908721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28262335496707089587939147 42393503245060634381908721)
                  ·
                    refine ⟨31795127433795475786431541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42393503245060634381908721 31795127433795475786431541)
                    ·
                      refine ⟨2980793196918325854977957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31795127433795475786431541 2980793196918325854977957)
                      ·
                        rfl

theorem cell23_5805074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_5805074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805074 prefixEnd_5805074 := by exact prefixLift 5805074
  have htrace : WordTrace (prefixWord ++ tailWord_5805074) baseStart_5805074 baseEnd_5805074 := by
    simpa [prefixWord, tailWord_5805074, baseEnd_5805074] using wordTrace_append hprefix tailTrace_5805074
  have hstable : (prefixWord ++ tailWord_5805074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805074).length < 2 ^ (prefixWord ++ tailWord_5805074).sum := by decide
  have hdescent : baseEnd_5805074 < baseStart_5805074 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805077 : List Nat := [1, 3, 2, 1, 4, 3, 1, 1, 3, 4]
def baseStart_5805077 : Nat := 118140960795 + 5805077 * 2 ^ 59
def prefixEnd_5805077 : Nat := 4983230072969 + 3 ^ 40 * 5805077 * 2
def baseEnd_5805077 : Nat := 993598245786763114413481

theorem tailTrace_5805077 : CollatzResearch.WordTrace tailWord_5805077 prefixEnd_5805077 993598245786763114413481 := by
  unfold tailWord_5805077
  simp only [CollatzResearch.WordTrace]
  refine ⟨211728552390204932065077485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141152368260136621376718323 211728552390204932065077485)
  ·
    refine ⟨79398207146326849524404057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211728552390204932065077485 79398207146326849524404057)
    ·
      refine ⟨59548655359745137143303043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79398207146326849524404057 59548655359745137143303043)
      ·
        refine ⟨89322983039617705714954565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59548655359745137143303043 89322983039617705714954565)
        ·
          refine ⟨16748059319928319821553981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89322983039617705714954565 16748059319928319821553981)
          ·
            refine ⟨6280522244973119933082743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16748059319928319821553981 6280522244973119933082743)
            ·
              refine ⟨9420783367459679899624115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6280522244973119933082743 9420783367459679899624115)
              ·
                refine ⟨14131175051189519849436173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9420783367459679899624115 14131175051189519849436173)
                ·
                  refine ⟨5299190644196069943538565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14131175051189519849436173 5299190644196069943538565)
                  ·
                    refine ⟨993598245786763114413481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5299190644196069943538565 993598245786763114413481)
                    ·
                      rfl

theorem cell23_5805077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 3, 4].length) (baseStart_5805077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805077 prefixEnd_5805077 := by exact prefixLift 5805077
  have htrace : WordTrace (prefixWord ++ tailWord_5805077) baseStart_5805077 baseEnd_5805077 := by
    simpa [prefixWord, tailWord_5805077, baseEnd_5805077] using wordTrace_append hprefix tailTrace_5805077
  have hstable : (prefixWord ++ tailWord_5805077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805077).length < 2 ^ (prefixWord ++ tailWord_5805077).sum := by decide
  have hdescent : baseEnd_5805077 < baseStart_5805077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805090 : List Nat := [3, 3, 1, 1, 1, 4, 1, 3, 6]
def baseStart_5805090 : Nat := 118140960795 + 5805090 * 2 ^ 59
def prefixEnd_5805090 : Nat := 4983230072969 + 3 ^ 40 * 5805090 * 2
def baseEnd_5805090 : Nat := 331200156956533088041987

theorem tailTrace_5805090 : CollatzResearch.WordTrace tailWord_5805090 prefixEnd_5805090 331200156956533088041987 := by
  unfold tailWord_5805090
  simp only [CollatzResearch.WordTrace]
  refine ⟨52932256634789458821325181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141152684359438556856867149 52932256634789458821325181)
  ·
    refine ⟨19849596238046047057996943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52932256634789458821325181 19849596238046047057996943)
    ·
      refine ⟨29774394357069070586995415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19849596238046047057996943 29774394357069070586995415)
      ·
        refine ⟨44661591535603605880493123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29774394357069070586995415 44661591535603605880493123)
        ·
          refine ⟨66992387303405408820739685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44661591535603605880493123 66992387303405408820739685)
          ·
            refine ⟨12561072619388514153888691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66992387303405408820739685 12561072619388514153888691)
            ·
              refine ⟨18841608929082771230833037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12561072619388514153888691 18841608929082771230833037)
              ·
                refine ⟨7065603348406039211562389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18841608929082771230833037 7065603348406039211562389)
                ·
                  refine ⟨331200156956533088041987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7065603348406039211562389 331200156956533088041987)
                  ·
                    rfl

theorem cell23_5805090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 3, 6].length) (baseStart_5805090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805090 prefixEnd_5805090 := by exact prefixLift 5805090
  have htrace : WordTrace (prefixWord ++ tailWord_5805090) baseStart_5805090 baseEnd_5805090 := by
    simpa [prefixWord, tailWord_5805090, baseEnd_5805090] using wordTrace_append hprefix tailTrace_5805090
  have hstable : (prefixWord ++ tailWord_5805090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805090).length < 2 ^ (prefixWord ++ tailWord_5805090).sum := by decide
  have hdescent : baseEnd_5805090 < baseStart_5805090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805100 : List Nat := [2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 3]
def baseStart_5805100 : Nat := 118140960795 + 5805100 * 2 ^ 59
def prefixEnd_5805100 : Nat := 4983230072969 + 3 ^ 40 * 5805100 * 2
def baseEnd_5805100 : Nat := 2980806547415342753252837

theorem tailTrace_5805100 : CollatzResearch.WordTrace tailWord_5805100 prefixEnd_5805100 2980806547415342753252837 := by
  unfold tailWord_5805100
  simp only [CollatzResearch.WordTrace]
  refine ⟨105864695634560803496582377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141152927512747737995443169 105864695634560803496582377)
  ·
    refine ⟨79398521725920602622436783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105864695634560803496582377 79398521725920602622436783)
    ·
      refine ⟨119097782588880903933655175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79398521725920602622436783 119097782588880903933655175)
      ·
        refine ⟨178646673883321355900482763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119097782588880903933655175 178646673883321355900482763)
        ·
          refine ⟨267970010824982033850724145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178646673883321355900482763 267970010824982033850724145)
          ·
            refine ⟨200977508118736525388043109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267970010824982033850724145 200977508118736525388043109)
            ·
              refine ⟨37683282772263098510258083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 200977508118736525388043109 37683282772263098510258083)
              ·
                refine ⟨56524924158394647765387125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37683282772263098510258083 56524924158394647765387125)
                ·
                  refine ⟨5299211639849498228005043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56524924158394647765387125 5299211639849498228005043)
                  ·
                    refine ⟨7948817459774247342007565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5299211639849498228005043 7948817459774247342007565)
                    ·
                      refine ⟨2980806547415342753252837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7948817459774247342007565 2980806547415342753252837)
                      ·
                        rfl

theorem cell23_5805100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 3].length) (baseStart_5805100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805100 prefixEnd_5805100 := by exact prefixLift 5805100
  have htrace : WordTrace (prefixWord ++ tailWord_5805100) baseStart_5805100 baseEnd_5805100 := by
    simpa [prefixWord, tailWord_5805100, baseEnd_5805100] using wordTrace_append hprefix tailTrace_5805100
  have hstable : (prefixWord ++ tailWord_5805100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805100).length < 2 ^ (prefixWord ++ tailWord_5805100).sum := by decide
  have hdescent : baseEnd_5805100 < baseStart_5805100 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805127 : List Nat := [1, 1, 4, 1, 3, 2, 2, 2, 2, 3, 2]
def baseStart_5805127 : Nat := 118140960795 + 5805127 * 2 ^ 59
def prefixEnd_5805127 : Nat := 4983230072969 + 3 ^ 40 * 5805127 * 2
def baseEnd_5805127 : Nat := 2980820411393014147615213

theorem tailTrace_5805127 : CollatzResearch.WordTrace tailWord_5805127 prefixEnd_5805127 2980820411393014147615213 := by
  unfold tailWord_5805127
  simp only [CollatzResearch.WordTrace]
  refine ⟨211730376040023790604397635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141153584026682527069598423 211730376040023790604397635)
  ·
    refine ⟨317595564060035685906596453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211730376040023790604397635 317595564060035685906596453)
    ·
      refine ⟨59549168261256691107486835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 317595564060035685906596453 59549168261256691107486835)
      ·
        refine ⟨89323752391885036661230253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59549168261256691107486835 89323752391885036661230253)
        ·
          refine ⟨33496407146956888747961345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89323752391885036661230253 33496407146956888747961345)
          ·
            refine ⟨25122305360217666560971009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33496407146956888747961345 25122305360217666560971009)
            ·
              refine ⟨18841729020163249920728257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25122305360217666560971009 18841729020163249920728257)
              ·
                refine ⟨14131296765122437440546193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18841729020163249920728257 14131296765122437440546193)
                ·
                  refine ⟨10598472573841828080409645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14131296765122437440546193 10598472573841828080409645)
                  ·
                    refine ⟨3974427215190685530153617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10598472573841828080409645 3974427215190685530153617)
                    ·
                      refine ⟨2980820411393014147615213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3974427215190685530153617 2980820411393014147615213)
                      ·
                        rfl

theorem cell23_5805127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 2, 3, 2].length) (baseStart_5805127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805127 prefixEnd_5805127 := by exact prefixLift 5805127
  have htrace : WordTrace (prefixWord ++ tailWord_5805127) baseStart_5805127 baseEnd_5805127 := by
    simpa [prefixWord, tailWord_5805127, baseEnd_5805127] using wordTrace_append hprefix tailTrace_5805127
  have hstable : (prefixWord ++ tailWord_5805127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805127).length < 2 ^ (prefixWord ++ tailWord_5805127).sum := by decide
  have hdescent : baseEnd_5805127 < baseStart_5805127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805134 : List Nat := [4, 1, 1, 1, 1, 3, 3, 4, 1, 1, 3]
def baseStart_5805134 : Nat := 118140960795 + 5805134 * 2 ^ 59
def prefixEnd_5805134 : Nat := 4983230072969 + 3 ^ 40 * 5805134 * 2
def baseEnd_5805134 : Nat := 2980824005757595620227681

theorem tailTrace_5805134 : CollatzResearch.WordTrace tailWord_5805134 prefixEnd_5805134 2980824005757595620227681 := by
  unfold tailWord_5805134
  simp only [CollatzResearch.WordTrace]
  refine ⟨26466328918874803849987807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141153754233998953866601637 26466328918874803849987807)
  ·
    refine ⟨39699493378312205774981711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26466328918874803849987807 39699493378312205774981711)
    ·
      refine ⟨59549240067468308662472567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39699493378312205774981711 59549240067468308662472567)
      ·
        refine ⟨89323860101202462993708851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59549240067468308662472567 89323860101202462993708851)
        ·
          refine ⟨133985790151803694490563277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89323860101202462993708851 133985790151803694490563277)
          ·
            refine ⟨50244671306926385433961229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133985790151803694490563277 50244671306926385433961229)
            ·
              refine ⟨18841751740097394537735461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50244671306926385433961229 18841751740097394537735461)
              ·
                refine ⟨3532828451268261475825399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18841751740097394537735461 3532828451268261475825399)
                ·
                  refine ⟨5299242676902392213738099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3532828451268261475825399 5299242676902392213738099)
                  ·
                    refine ⟨7948864015353588320607149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5299242676902392213738099 7948864015353588320607149)
                    ·
                      refine ⟨2980824005757595620227681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7948864015353588320607149 2980824005757595620227681)
                      ·
                        rfl

theorem cell23_5805134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 4, 1, 1, 3].length) (baseStart_5805134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805134 prefixEnd_5805134 := by exact prefixLift 5805134
  have htrace : WordTrace (prefixWord ++ tailWord_5805134) baseStart_5805134 baseEnd_5805134 := by
    simpa [prefixWord, tailWord_5805134, baseEnd_5805134] using wordTrace_append hprefix tailTrace_5805134
  have hstable : (prefixWord ++ tailWord_5805134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805134).length < 2 ^ (prefixWord ++ tailWord_5805134).sum := by decide
  have hdescent : baseEnd_5805134 < baseStart_5805134 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805140 : List Nat := [2, 4, 1, 1, 1, 1, 3, 2, 3, 1, 4]
def baseStart_5805140 : Nat := 118140960795 + 5805140 * 2 ^ 59
def prefixEnd_5805140 : Nat := 4983230072969 + 3 ^ 40 * 5805140 * 2
def baseEnd_5805140 : Nat := 2980827086641522596752653

theorem tailTrace_5805140 : CollatzResearch.WordTrace tailWord_5805140 prefixEnd_5805140 2980827086641522596752653 := by
  unfold tailWord_5805140
  simp only [CollatzResearch.WordTrace]
  refine ⟨105865425094488346912310437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141153900125984462549747249 105865425094488346912310437)
  ·
    refine ⟨19849767205216565046058207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105865425094488346912310437 19849767205216565046058207)
    ·
      refine ⟨29774650807824847569087311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19849767205216565046058207 29774650807824847569087311)
      ·
        refine ⟨44661976211737271353630967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29774650807824847569087311 44661976211737271353630967)
        ·
          refine ⟨66992964317605907030446451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44661976211737271353630967 66992964317605907030446451)
          ·
            refine ⟨100489446476408860545669677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66992964317605907030446451 100489446476408860545669677)
            ·
              refine ⟨37683542428653322704626129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100489446476408860545669677 37683542428653322704626129)
              ·
                refine ⟨28262656821489992028469597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37683542428653322704626129 28262656821489992028469597)
                ·
                  refine ⟨10598496308058747010676099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28262656821489992028469597 10598496308058747010676099)
                  ·
                    refine ⟨15897744462088120516014149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10598496308058747010676099 15897744462088120516014149)
                    ·
                      refine ⟨2980827086641522596752653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15897744462088120516014149 2980827086641522596752653)
                      ·
                        rfl

theorem cell23_5805140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_5805140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805140 prefixEnd_5805140 := by exact prefixLift 5805140
  have htrace : WordTrace (prefixWord ++ tailWord_5805140) baseStart_5805140 baseEnd_5805140 := by
    simpa [prefixWord, tailWord_5805140, baseEnd_5805140] using wordTrace_append hprefix tailTrace_5805140
  have hstable : (prefixWord ++ tailWord_5805140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805140).length < 2 ^ (prefixWord ++ tailWord_5805140).sum := by decide
  have hdescent : baseEnd_5805140 < baseStart_5805140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805143 : List Nat := [1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 5]
def baseStart_5805143 : Nat := 118140960795 + 5805143 * 2 ^ 59
def prefixEnd_5805143 : Nat := 4983230072969 + 3 ^ 40 * 5805143 * 2
def baseEnd_5805143 : Nat := 2980828627083486085015139

theorem tailTrace_5805143 : CollatzResearch.WordTrace tailWord_5805143 prefixEnd_5805143 2980828627083486085015139 := by
  unfold tailWord_5805143
  simp only [CollatzResearch.WordTrace]
  refine ⟨211730959607965825336980083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141153973071977216891320055 211730959607965825336980083)
  ·
    refine ⟨317596439411948738005470125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211730959607965825336980083 317596439411948738005470125)
    ·
      refine ⟨119098664779480776752051297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 317596439411948738005470125 119098664779480776752051297)
      ·
        refine ⟨89323998584610582564038473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119098664779480776752051297 89323998584610582564038473)
        ·
          refine ⟨66992998938457936923028855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89323998584610582564038473 66992998938457936923028855)
          ·
            refine ⟨100489498407686905384543283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66992998938457936923028855 100489498407686905384543283)
            ·
              refine ⟨150734247611530358076814925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100489498407686905384543283 150734247611530358076814925)
              ·
                refine ⟨56525342854323884278805597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150734247611530358076814925 56525342854323884278805597)
                ·
                  refine ⟨21197003570371456604552099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56525342854323884278805597 21197003570371456604552099)
                  ·
                    refine ⟨31795505355557184906828149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21197003570371456604552099 31795505355557184906828149)
                    ·
                      refine ⟨2980828627083486085015139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31795505355557184906828149 2980828627083486085015139)
                      ·
                        rfl

theorem cell23_5805143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_5805143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805143 prefixEnd_5805143 := by exact prefixLift 5805143
  have htrace : WordTrace (prefixWord ++ tailWord_5805143) baseStart_5805143 baseEnd_5805143 := by
    simpa [prefixWord, tailWord_5805143, baseEnd_5805143] using wordTrace_append hprefix tailTrace_5805143
  have hstable : (prefixWord ++ tailWord_5805143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805143).length < 2 ^ (prefixWord ++ tailWord_5805143).sum := by decide
  have hdescent : baseEnd_5805143 < baseStart_5805143 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805153 : List Nat := [1, 2, 3, 1, 1, 2, 2, 3, 1, 1, 6]
def baseStart_5805153 : Nat := 118140960795 + 5805153 * 2 ^ 59
def prefixEnd_5805153 : Nat := 4983230072969 + 3 ^ 40 * 5805153 * 2
def baseEnd_5805153 : Nat := 2980833761890031045890093

theorem tailTrace_5805153 : CollatzResearch.WordTrace tailWord_5805153 prefixEnd_5805153 2980833761890031045890093 := by
  unfold tailWord_5805153
  simp only [CollatzResearch.WordTrace]
  refine ⟨211731324337929597044844113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141154216225286398029896075 211731324337929597044844113)
  ·
    refine ⟨158798493253447197783633085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211731324337929597044844113 158798493253447197783633085)
    ·
      refine ⟨59549434970042699168862407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158798493253447197783633085 59549434970042699168862407)
      ·
        refine ⟨89324152455064048753293611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59549434970042699168862407 89324152455064048753293611)
        ·
          refine ⟨133986228682596073129940417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89324152455064048753293611 133986228682596073129940417)
          ·
            refine ⟨100489671511947054847455313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133986228682596073129940417 100489671511947054847455313)
            ·
              refine ⟨75367253633960291135591485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100489671511947054847455313 75367253633960291135591485)
              ·
                refine ⟨28262720112735109175846807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75367253633960291135591485 28262720112735109175846807)
                ·
                  refine ⟨42394080169102663763770211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28262720112735109175846807 42394080169102663763770211)
                  ·
                    refine ⟨63591120253653995645655317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42394080169102663763770211 63591120253653995645655317)
                    ·
                      refine ⟨2980833761890031045890093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63591120253653995645655317 2980833761890031045890093)
                      ·
                        rfl

theorem cell23_5805153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_5805153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805153 prefixEnd_5805153 := by exact prefixLift 5805153
  have htrace : WordTrace (prefixWord ++ tailWord_5805153) baseStart_5805153 baseEnd_5805153 := by
    simpa [prefixWord, tailWord_5805153, baseEnd_5805153] using wordTrace_append hprefix tailTrace_5805153
  have hstable : (prefixWord ++ tailWord_5805153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805153).length < 2 ^ (prefixWord ++ tailWord_5805153).sum := by decide
  have hdescent : baseEnd_5805153 < baseStart_5805153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805170 : List Nat := [3, 2, 1, 2, 2, 1, 1, 4, 1, 2, 4]
def baseStart_5805170 : Nat := 118140960795 + 5805170 * 2 ^ 59
def prefixEnd_5805170 : Nat := 4983230072969 + 3 ^ 40 * 5805170 * 2
def baseEnd_5805170 : Nat := 2980842491061157479377515

theorem tailTrace_5805170 : CollatzResearch.WordTrace tailWord_5805170 prefixEnd_5805170 2980842491061157479377515 := by
  unfold tailWord_5805170
  simp only [CollatzResearch.WordTrace]
  refine ⟨52932986094717002237053241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141154629585912005965475309 52932986094717002237053241)
  ·
    refine ⟨39699739571037751677789931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52932986094717002237053241 39699739571037751677789931)
    ·
      refine ⟨59549609356556627516684897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39699739571037751677789931 59549609356556627516684897)
      ·
        refine ⟨44662207017417470637513673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59549609356556627516684897 44662207017417470637513673)
        ·
          refine ⟨33496655263063102978135255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44662207017417470637513673 33496655263063102978135255)
          ·
            refine ⟨50244982894594654467202883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33496655263063102978135255 50244982894594654467202883)
            ·
              refine ⟨75367474341891981700804325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50244982894594654467202883 75367474341891981700804325)
              ·
                refine ⟨14131401439104746568900811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75367474341891981700804325 14131401439104746568900811)
                ·
                  refine ⟨21197102158657119853351217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14131401439104746568900811 21197102158657119853351217)
                  ·
                    refine ⟨15897826618992839890013413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21197102158657119853351217 15897826618992839890013413)
                    ·
                      refine ⟨2980842491061157479377515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15897826618992839890013413 2980842491061157479377515)
                      ·
                        rfl

theorem cell23_5805170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_5805170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805170 prefixEnd_5805170 := by exact prefixLift 5805170
  have htrace : WordTrace (prefixWord ++ tailWord_5805170) baseStart_5805170 baseEnd_5805170 := by
    simpa [prefixWord, tailWord_5805170, baseEnd_5805170] using wordTrace_append hprefix tailTrace_5805170
  have hstable : (prefixWord ++ tailWord_5805170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805170).length < 2 ^ (prefixWord ++ tailWord_5805170).sum := by decide
  have hdescent : baseEnd_5805170 < baseStart_5805170 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805174 : List Nat := [5, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2]
def baseStart_5805174 : Nat := 118140960795 + 5805174 * 2 ^ 59
def prefixEnd_5805174 : Nat := 4983230072969 + 3 ^ 40 * 5805174 * 2
def baseEnd_5805174 : Nat := 2980844544983775463727497

theorem tailTrace_5805174 : CollatzResearch.WordTrace tailWord_5805174 prefixEnd_5805174 2980844544983775463727497 := by
  unfold tailWord_5805174
  simp only [CollatzResearch.WordTrace]
  refine ⟨13233255641928344851959911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141154726847235678420905717 13233255641928344851959911)
  ·
    refine ⟨19849883462892517277939867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13233255641928344851959911 19849883462892517277939867)
    ·
      refine ⟨29774825194338775916909801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19849883462892517277939867 29774825194338775916909801)
      ·
        refine ⟨22331118895754081937682351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29774825194338775916909801 22331118895754081937682351)
        ·
          refine ⟨33496678343631122906523527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22331118895754081937682351 33496678343631122906523527)
          ·
            refine ⟨50245017515446684359785291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33496678343631122906523527 50245017515446684359785291)
            ·
              refine ⟨75367526273170026539677937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50245017515446684359785291 75367526273170026539677937)
              ·
                refine ⟨56525644704877519904758453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75367526273170026539677937 56525644704877519904758453)
                ·
                  refine ⟨5299279191082267491071105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56525644704877519904758453 5299279191082267491071105)
                  ·
                    refine ⟨3974459393311700618303329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5299279191082267491071105 3974459393311700618303329)
                    ·
                      refine ⟨2980844544983775463727497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3974459393311700618303329 2980844544983775463727497)
                      ·
                        rfl

theorem cell23_5805174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_5805174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805174 prefixEnd_5805174 := by exact prefixLift 5805174
  have htrace : WordTrace (prefixWord ++ tailWord_5805174) baseStart_5805174 baseEnd_5805174 := by
    simpa [prefixWord, tailWord_5805174, baseEnd_5805174] using wordTrace_append hprefix tailTrace_5805174
  have hstable : (prefixWord ++ tailWord_5805174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805174).length < 2 ^ (prefixWord ++ tailWord_5805174).sum := by decide
  have hdescent : baseEnd_5805174 < baseStart_5805174 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805200 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 2, 7, 2]
def baseStart_5805200 : Nat := 118140960795 + 5805200 * 2 ^ 59
def prefixEnd_5805200 : Nat := 4983230072969 + 3 ^ 40 * 5805200 * 2
def baseEnd_5805200 : Nat := 2980857895480792362002377

theorem tailTrace_5805200 : CollatzResearch.WordTrace tailWord_5805200 prefixEnd_5805200 2980857895480792362002377 := by
  unfold tailWord_5805200
  simp only [CollatzResearch.WordTrace]
  refine ⟨105866519284379662035902527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141155359045839549381203369 105866519284379662035902527)
  ·
    refine ⟨158799778926569493053853791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105866519284379662035902527 158799778926569493053853791)
    ·
      refine ⟨238199668389854239580780687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158799778926569493053853791 238199668389854239580780687)
      ·
        refine ⟨357299502584781359371171031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238199668389854239580780687 357299502584781359371171031)
        ·
          refine ⟨535949253877172039056756547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357299502584781359371171031 535949253877172039056756547)
          ·
            refine ⟨803923880815758058585134821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 535949253877172039056756547 803923880815758058585134821)
            ·
              refine ⟨150735727652954635984712779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 803923880815758058585134821 150735727652954635984712779)
              ·
                refine ⟨226103591479431953977069169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150735727652954635984712779 226103591479431953977069169)
                ·
                  refine ⟨169577693609573965482801877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 226103591479431953977069169 169577693609573965482801877)
                  ·
                    refine ⟨3974477193974389816003169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 169577693609573965482801877 3974477193974389816003169)
                    ·
                      refine ⟨2980857895480792362002377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3974477193974389816003169 2980857895480792362002377)
                      ·
                        rfl

theorem cell23_5805200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 2, 7, 2].length) (baseStart_5805200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805200 prefixEnd_5805200 := by exact prefixLift 5805200
  have htrace : WordTrace (prefixWord ++ tailWord_5805200) baseStart_5805200 baseEnd_5805200 := by
    simpa [prefixWord, tailWord_5805200, baseEnd_5805200] using wordTrace_append hprefix tailTrace_5805200
  have hstable : (prefixWord ++ tailWord_5805200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805200).length < 2 ^ (prefixWord ++ tailWord_5805200).sum := by decide
  have hdescent : baseEnd_5805200 < baseStart_5805200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805207 : List Nat := [1, 1, 3, 3, 3, 1, 3, 1, 1, 3, 3]
def baseStart_5805207 : Nat := 118140960795 + 5805207 * 2 ^ 59
def prefixEnd_5805207 : Nat := 4983230072969 + 3 ^ 40 * 5805207 * 2
def baseEnd_5805207 : Nat := 2980861489845373834614845

theorem tailTrace_5805207 : CollatzResearch.WordTrace tailWord_5805207 prefixEnd_5805207 2980861489845373834614845 := by
  unfold tailWord_5805207
  simp only [CollatzResearch.WordTrace]
  refine ⟨211733293879733964267309875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141155529253155976178206583 211733293879733964267309875)
  ·
    refine ⟨317599940819600946400964813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211733293879733964267309875 317599940819600946400964813)
    ·
      refine ⟨119099977807350354900361805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 317599940819600946400964813 119099977807350354900361805)
      ·
        refine ⟨44662491677756383087635677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119099977807350354900361805 44662491677756383087635677)
        ·
          refine ⟨16748434379158643657863379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44662491677756383087635677 16748434379158643657863379)
          ·
            refine ⟨25122651568737965486795069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16748434379158643657863379 25122651568737965486795069)
            ·
              refine ⟨9420994338276737057548151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25122651568737965486795069 9420994338276737057548151)
              ·
                refine ⟨14131491507415105586322227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9420994338276737057548151 14131491507415105586322227)
                ·
                  refine ⟨21197237261122658379483341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14131491507415105586322227 21197237261122658379483341)
                  ·
                    refine ⟨7948963972920996892306253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21197237261122658379483341 7948963972920996892306253)
                    ·
                      refine ⟨2980861489845373834614845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7948963972920996892306253 2980861489845373834614845)
                      ·
                        rfl

theorem cell23_5805207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_5805207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805207 prefixEnd_5805207 := by exact prefixLift 5805207
  have htrace : WordTrace (prefixWord ++ tailWord_5805207) baseStart_5805207 baseEnd_5805207 := by
    simpa [prefixWord, tailWord_5805207, baseEnd_5805207] using wordTrace_append hprefix tailTrace_5805207
  have hstable : (prefixWord ++ tailWord_5805207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805207).length < 2 ^ (prefixWord ++ tailWord_5805207).sum := by decide
  have hdescent : baseEnd_5805207 < baseStart_5805207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805214 : List Nat := [4, 3, 1, 1, 2, 3, 2, 7]
def baseStart_5805214 : Nat := 118140960795 + 5805214 * 2 ^ 59
def prefixEnd_5805214 : Nat := 4983230072969 + 3 ^ 40 * 5805214 * 2
def baseEnd_5805214 : Nat := 110402410526294641008419

theorem tailTrace_5805214 : CollatzResearch.WordTrace tailWord_5805214 prefixEnd_5805214 110402410526294641008419 := by
  unfold tailWord_5805214
  simp only [CollatzResearch.WordTrace]
  refine ⟨26466693648838575557851837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141155699460472402975209797 26466693648838575557851837)
  ·
    refine ⟨9925010118314465834194439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26466693648838575557851837 9925010118314465834194439)
    ·
      refine ⟨14887515177471698751291659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9925010118314465834194439 14887515177471698751291659)
      ·
        refine ⟨22331272766207548126937489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14887515177471698751291659 22331272766207548126937489)
        ·
          refine ⟨16748454574655661095203117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22331272766207548126937489 16748454574655661095203117)
          ·
            refine ⟨6280670465495872910701169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16748454574655661095203117 6280670465495872910701169)
            ·
              refine ⟨4710502849121904683025877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6280670465495872910701169 4710502849121904683025877)
              ·
                refine ⟨110402410526294641008419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4710502849121904683025877 110402410526294641008419)
                ·
                  rfl

theorem cell23_5805214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 7].length) (baseStart_5805214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805214 prefixEnd_5805214 := by exact prefixLift 5805214
  have htrace : WordTrace (prefixWord ++ tailWord_5805214) baseStart_5805214 baseEnd_5805214 := by
    simpa [prefixWord, tailWord_5805214, baseEnd_5805214] using wordTrace_append hprefix tailTrace_5805214
  have hstable : (prefixWord ++ tailWord_5805214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805214).length < 2 ^ (prefixWord ++ tailWord_5805214).sum := by decide
  have hdescent : baseEnd_5805214 < baseStart_5805214 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805220 : List Nat := [2, 3, 1, 2, 3, 1, 1, 1, 2, 2, 5]
def baseStart_5805220 : Nat := 118140960795 + 5805220 * 2 ^ 59
def prefixEnd_5805220 : Nat := 4983230072969 + 3 ^ 40 * 5805220 * 2
def baseEnd_5805220 : Nat := 2980868165093882283752285

theorem tailTrace_5805220 : CollatzResearch.WordTrace tailWord_5805220 prefixEnd_5805220 2980868165093882283752285 := by
  unfold tailWord_5805220
  simp only [CollatzResearch.WordTrace]
  refine ⟨105866884014343433743766557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141155845352457911658355409 105866884014343433743766557)
  ·
    refine ⟨39700081505378787653912459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105866884014343433743766557 39700081505378787653912459)
    ·
      refine ⟨59550122258068181480868689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39700081505378787653912459 59550122258068181480868689)
      ·
        refine ⟨44662591693551136110651517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59550122258068181480868689 44662591693551136110651517)
        ·
          refine ⟨16748471885081676041494319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44662591693551136110651517 16748471885081676041494319)
          ·
            refine ⟨25122707827622514062241479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16748471885081676041494319 25122707827622514062241479)
            ·
              refine ⟨37684061741433771093362219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25122707827622514062241479 37684061741433771093362219)
              ·
                refine ⟨56526092612150656640043329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37684061741433771093362219 56526092612150656640043329)
                ·
                  refine ⟨42394569459112992480032497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56526092612150656640043329 42394569459112992480032497)
                  ·
                    refine ⟨31795927094334744360024373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42394569459112992480032497 31795927094334744360024373)
                    ·
                      refine ⟨2980868165093882283752285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31795927094334744360024373 2980868165093882283752285)
                      ·
                        rfl

theorem cell23_5805220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_5805220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805220 prefixEnd_5805220 := by exact prefixLift 5805220
  have htrace : WordTrace (prefixWord ++ tailWord_5805220) baseStart_5805220 baseEnd_5805220 := by
    simpa [prefixWord, tailWord_5805220, baseEnd_5805220] using wordTrace_append hprefix tailTrace_5805220
  have hstable : (prefixWord ++ tailWord_5805220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805220).length < 2 ^ (prefixWord ++ tailWord_5805220).sum := by decide
  have hdescent : baseEnd_5805220 < baseStart_5805220 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805234 : List Nat := [3, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2]
def baseStart_5805234 : Nat := 118140960795 + 5805234 * 2 ^ 59
def prefixEnd_5805234 : Nat := 4983230072969 + 3 ^ 40 * 5805234 * 2
def baseEnd_5805234 : Nat := 2980875353823045228977221

theorem tailTrace_5805234 : CollatzResearch.WordTrace tailWord_5805234 prefixEnd_5805234 2980875353823045228977221 := by
  unfold tailWord_5805234
  simp only [CollatzResearch.WordTrace]
  refine ⟨52933569662659036969635689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141156185767090765252361837 52933569662659036969635689)
  ·
    refine ⟨39700177246994277727226767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52933569662659036969635689 39700177246994277727226767)
    ·
      refine ⟨59550265870491416590840151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39700177246994277727226767 59550265870491416590840151)
      ·
        refine ⟨89325398805737124886260227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59550265870491416590840151 89325398805737124886260227)
        ·
          refine ⟨133988098208605687329390341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89325398805737124886260227 133988098208605687329390341)
          ·
            refine ⟨25122768414113566374260689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 133988098208605687329390341 25122768414113566374260689)
            ·
              refine ⟨18842076310585174780695517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25122768414113566374260689 18842076310585174780695517)
              ·
                refine ⟨7065778616469440542760819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18842076310585174780695517 7065778616469440542760819)
                ·
                  refine ⟨10598667924704160814141229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7065778616469440542760819 10598667924704160814141229)
                  ·
                    refine ⟨3974500471764060305302961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10598667924704160814141229 3974500471764060305302961)
                    ·
                      refine ⟨2980875353823045228977221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3974500471764060305302961 2980875353823045228977221)
                      ·
                        rfl

theorem cell23_5805234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2].length) (baseStart_5805234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805234 prefixEnd_5805234 := by exact prefixLift 5805234
  have htrace : WordTrace (prefixWord ++ tailWord_5805234) baseStart_5805234 baseEnd_5805234 := by
    simpa [prefixWord, tailWord_5805234, baseEnd_5805234] using wordTrace_append hprefix tailTrace_5805234
  have hstable : (prefixWord ++ tailWord_5805234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805234).length < 2 ^ (prefixWord ++ tailWord_5805234).sum := by decide
  have hdescent : baseEnd_5805234 < baseStart_5805234 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805243 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 6]
def baseStart_5805243 : Nat := 118140960795 + 5805243 * 2 ^ 59
def prefixEnd_5805243 : Nat := 4983230072969 + 3 ^ 40 * 5805243 * 2
def baseEnd_5805243 : Nat := 2980879975148935693764679

theorem tailTrace_5805243 : CollatzResearch.WordTrace tailWord_5805243 prefixEnd_5805243 2980879975148935693764679 := by
  unfold tailWord_5805243
  simp only [CollatzResearch.WordTrace]
  refine ⟨211734606907603542415620383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141156404605069028277080255 211734606907603542415620383)
  ·
    refine ⟨317601910361405313623430575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211734606907603542415620383 317601910361405313623430575)
    ·
      refine ⟨476402865542107970435145863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317601910361405313623430575 476402865542107970435145863)
      ·
        refine ⟨714604298313161955652718795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 476402865542107970435145863 714604298313161955652718795)
        ·
          refine ⟨1071906447469742933479078193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 714604298313161955652718795 1071906447469742933479078193)
          ·
            refine ⟨803929835602307200109308645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1071906447469742933479078193 803929835602307200109308645)
            ·
              refine ⟨150736844175432600020495371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 803929835602307200109308645 150736844175432600020495371)
              ·
                refine ⟨226105266263148900030743057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150736844175432600020495371 226105266263148900030743057)
                ·
                  refine ⟨169578949697361675023057293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 226105266263148900030743057 169578949697361675023057293)
                  ·
                    refine ⟨63592106136510628133646485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 169578949697361675023057293 63592106136510628133646485)
                    ·
                      refine ⟨2980879975148935693764679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63592106136510628133646485 2980879975148935693764679)
                      ·
                        rfl

theorem cell23_5805243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 6].length) (baseStart_5805243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805243 prefixEnd_5805243 := by exact prefixLift 5805243
  have htrace : WordTrace (prefixWord ++ tailWord_5805243) baseStart_5805243 baseEnd_5805243 := by
    simpa [prefixWord, tailWord_5805243, baseEnd_5805243] using wordTrace_append hprefix tailTrace_5805243
  have hstable : (prefixWord ++ tailWord_5805243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805243).length < 2 ^ (prefixWord ++ tailWord_5805243).sum := by decide
  have hdescent : baseEnd_5805243 < baseStart_5805243 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805298 : List Nat := [3, 2, 1, 3, 3, 1, 2, 2, 2, 2, 2]
def baseStart_5805298 : Nat := 118140960795 + 5805298 * 2 ^ 59
def prefixEnd_5805298 : Nat := 4983230072969 + 3 ^ 40 * 5805298 * 2
def baseEnd_5805298 : Nat := 2980908216584932978576927

theorem tailTrace_5805298 : CollatzResearch.WordTrace tailWord_5805298 prefixEnd_5805298 2980908216584932978576927 := by
  unfold tailWord_5805298
  simp only [CollatzResearch.WordTrace]
  refine ⟨52934153230601071702218137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141157741948269524539248365 52934153230601071702218137)
  ·
    refine ⟨39700614922950803776663603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52934153230601071702218137 39700614922950803776663603)
    ·
      refine ⟨59550922384426205664995405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39700614922950803776663603 59550922384426205664995405)
      ·
        refine ⟨22331595894159827124373277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59550922384426205664995405 22331595894159827124373277)
        ·
          refine ⟨8374348460309935171639979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22331595894159827124373277 8374348460309935171639979)
          ·
            refine ⟨12561522690464902757459969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8374348460309935171639979 12561522690464902757459969)
            ·
              refine ⟨9421142017848677068094977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12561522690464902757459969 9421142017848677068094977)
              ·
                refine ⟨7065856513386507801071233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9421142017848677068094977 7065856513386507801071233)
                ·
                  refine ⟨5299392385039880850803425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7065856513386507801071233 5299392385039880850803425)
                  ·
                    refine ⟨3974544288779910638102569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5299392385039880850803425 3974544288779910638102569)
                    ·
                      refine ⟨2980908216584932978576927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3974544288779910638102569 2980908216584932978576927)
                      ·
                        rfl

theorem cell23_5805298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_5805298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805298 prefixEnd_5805298 := by exact prefixLift 5805298
  have htrace : WordTrace (prefixWord ++ tailWord_5805298) baseStart_5805298 baseEnd_5805298 := by
    simpa [prefixWord, tailWord_5805298, baseEnd_5805298] using wordTrace_append hprefix tailTrace_5805298
  have hstable : (prefixWord ++ tailWord_5805298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805298).length < 2 ^ (prefixWord ++ tailWord_5805298).sum := by decide
  have hdescent : baseEnd_5805298 < baseStart_5805298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805360 : List Nat := [2, 1, 1, 1, 2, 2, 5, 1, 8]
def baseStart_5805360 : Nat := 118140960795 + 5805360 * 2 ^ 59
def prefixEnd_5805360 : Nat := 4983230072969 + 3 ^ 40 * 5805360 * 2
def baseEnd_5805360 : Nat := 331215561376167970666849

theorem tailTrace_5805360 : CollatzResearch.WordTrace tailWord_5805360 prefixEnd_5805360 331215561376167970666849 := by
  unfold tailWord_5805360
  simp only [CollatzResearch.WordTrace]
  refine ⟨105869437124089835698814767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141159249498786447598419689 105869437124089835698814767)
  ·
    refine ⟨158804155686134753548222151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105869437124089835698814767 158804155686134753548222151)
    ·
      refine ⟨238206233529202130322333227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158804155686134753548222151 238206233529202130322333227)
      ·
        refine ⟨357309350293803195483499841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238206233529202130322333227 357309350293803195483499841)
        ·
          refine ⟨267982012720352396612624881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 357309350293803195483499841 267982012720352396612624881)
          ·
            refine ⟨200986509540264297459468661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267982012720352396612624881 200986509540264297459468661)
            ·
              refine ⟨18842485269399777886825187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 200986509540264297459468661 18842485269399777886825187)
              ·
                refine ⟨28263727904099666830237781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18842485269399777886825187 28263727904099666830237781)
                ·
                  refine ⟨331215561376167970666849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28263727904099666830237781 331215561376167970666849)
                  ·
                    rfl

theorem cell23_5805360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 8].length) (baseStart_5805360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805360 prefixEnd_5805360 := by exact prefixLift 5805360
  have htrace : WordTrace (prefixWord ++ tailWord_5805360) baseStart_5805360 baseEnd_5805360 := by
    simpa [prefixWord, tailWord_5805360, baseEnd_5805360] using wordTrace_append hprefix tailTrace_5805360
  have hstable : (prefixWord ++ tailWord_5805360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805360).length < 2 ^ (prefixWord ++ tailWord_5805360).sum := by decide
  have hdescent : baseEnd_5805360 < baseStart_5805360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805421 : List Nat := [1, 5, 1, 1, 1, 3, 3, 1, 3, 1, 3]
def baseStart_5805421 : Nat := 118140960795 + 5805421 * 2 ^ 59
def prefixEnd_5805421 : Nat := 4983230072969 + 3 ^ 40 * 5805421 * 2
def baseEnd_5805421 : Nat := 2980971374705435997338861

theorem tailTrace_5805421 : CollatzResearch.WordTrace tailWord_5805421 prefixEnd_5805421 2980971374705435997338861 := by
  unfold tailWord_5805421
  simp only [CollatzResearch.WordTrace]
  refine ⟨211741099100958678815600117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141160732733972452543733411 211741099100958678815600117)
  ·
    refine ⟨19850728040714876138962511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 211741099100958678815600117 19850728040714876138962511)
    ·
      refine ⟨29776092061072314208443767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19850728040714876138962511 29776092061072314208443767)
      ·
        refine ⟨44664138091608471312665651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29776092061072314208443767 44664138091608471312665651)
        ·
          refine ⟨66996207137412706968998477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44664138091608471312665651 66996207137412706968998477)
          ·
            refine ⟨25123577676529765113374429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66996207137412706968998477 25123577676529765113374429)
            ·
              refine ⟨9421341628698661917515411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25123577676529765113374429 9421341628698661917515411)
              ·
                refine ⟨14132012443047992876273117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9421341628698661917515411 14132012443047992876273117)
                ·
                  refine ⟨5299504666142997328602419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14132012443047992876273117 5299504666142997328602419)
                  ·
                    refine ⟨7949256999214495992903629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5299504666142997328602419 7949256999214495992903629)
                    ·
                      refine ⟨2980971374705435997338861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7949256999214495992903629 2980971374705435997338861)
                      ·
                        rfl

theorem cell23_5805421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_5805421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805421 prefixEnd_5805421 := by exact prefixLift 5805421
  have htrace : WordTrace (prefixWord ++ tailWord_5805421) baseStart_5805421 baseEnd_5805421 := by
    simpa [prefixWord, tailWord_5805421, baseEnd_5805421] using wordTrace_append hprefix tailTrace_5805421
  have hstable : (prefixWord ++ tailWord_5805421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805421).length < 2 ^ (prefixWord ++ tailWord_5805421).sum := by decide
  have hdescent : baseEnd_5805421 < baseStart_5805421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805437 : List Nat := [1, 4, 1, 1, 2, 2, 2, 3, 1, 6]
def baseStart_5805437 : Nat := 118140960795 + 5805437 * 2 ^ 59
def prefixEnd_5805437 : Nat := 4983230072969 + 3 ^ 40 * 5805437 * 2
def baseEnd_5805437 : Nat := 993659863465302644912929

theorem tailTrace_5805437 : CollatzResearch.WordTrace tailWord_5805437 prefixEnd_5805437 993659863465302644912929 := by
  unfold tailWord_5805437
  simp only [CollatzResearch.WordTrace]
  refine ⟨211741682668900713548182565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141161121779267142365455043 211741682668900713548182565)
  ·
    refine ⟨39701565500418883790284231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 211741682668900713548182565 39701565500418883790284231)
    ·
      refine ⟨59552348250628325685426347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39701565500418883790284231 59552348250628325685426347)
      ·
        refine ⟨89328522375942488528139521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59552348250628325685426347 89328522375942488528139521)
        ·
          refine ⟨66996391781956866396104641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89328522375942488528139521 66996391781956866396104641)
          ·
            refine ⟨50247293836467649797078481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66996391781956866396104641 50247293836467649797078481)
            ·
              refine ⟨37685470377350737347808861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50247293836467649797078481 37685470377350737347808861)
              ·
                refine ⟨14132051391506526505428323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37685470377350737347808861 14132051391506526505428323)
                ·
                  refine ⟨21198077087259789758142485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14132051391506526505428323 21198077087259789758142485)
                  ·
                    refine ⟨993659863465302644912929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21198077087259789758142485 993659863465302644912929)
                    ·
                      rfl

theorem cell23_5805437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 6].length) (baseStart_5805437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805437 prefixEnd_5805437 := by exact prefixLift 5805437
  have htrace : WordTrace (prefixWord ++ tailWord_5805437) baseStart_5805437 baseEnd_5805437 := by
    simpa [prefixWord, tailWord_5805437, baseEnd_5805437] using wordTrace_append hprefix tailTrace_5805437
  have hstable : (prefixWord ++ tailWord_5805437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805437).length < 2 ^ (prefixWord ++ tailWord_5805437).sum := by decide
  have hdescent : baseEnd_5805437 < baseStart_5805437 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805444 : List Nat := [2, 3, 2, 1, 1, 4, 1, 1, 3, 1, 4]
def baseStart_5805444 : Nat := 118140960795 + 5805444 * 2 ^ 59
def prefixEnd_5805444 : Nat := 4983230072969 + 3 ^ 40 * 5805444 * 2
def baseEnd_5805444 : Nat := 2980983184760489407351255

theorem tailTrace_5805444 : CollatzResearch.WordTrace tailWord_5805444 prefixEnd_5805444 2980983184760489407351255 := by
  unfold tailWord_5805444
  simp only [CollatzResearch.WordTrace]
  refine ⟨105870968989937676871843693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141161291986583569162458257 105870968989937676871843693)
  ·
    refine ⟨39701613371226628826941385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105870968989937676871843693 39701613371226628826941385)
    ·
      refine ⟨29776210028419971620206039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39701613371226628826941385 29776210028419971620206039)
      ·
        refine ⟨44664315042629957430309059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29776210028419971620206039 44664315042629957430309059)
        ·
          refine ⟨66996472563944936145463589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44664315042629957430309059 66996472563944936145463589)
          ·
            refine ⟨12561838605739675527274423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66996472563944936145463589 12561838605739675527274423)
            ·
              refine ⟨18842757908609513290911635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12561838605739675527274423 18842757908609513290911635)
              ·
                refine ⟨28264136862914269936367453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18842757908609513290911635 28264136862914269936367453)
                ·
                  refine ⟨10599051323592851226137795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28264136862914269936367453 10599051323592851226137795)
                  ·
                    refine ⟨15898576985389276839206693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10599051323592851226137795 15898576985389276839206693)
                    ·
                      refine ⟨2980983184760489407351255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15898576985389276839206693 2980983184760489407351255)
                      ·
                        rfl

theorem cell23_5805444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_5805444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805444 prefixEnd_5805444 := by exact prefixLift 5805444
  have htrace : WordTrace (prefixWord ++ tailWord_5805444) baseStart_5805444 baseEnd_5805444 := by
    simpa [prefixWord, tailWord_5805444, baseEnd_5805444] using wordTrace_append hprefix tailTrace_5805444
  have hstable : (prefixWord ++ tailWord_5805444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805444).length < 2 ^ (prefixWord ++ tailWord_5805444).sum := by decide
  have hdescent : baseEnd_5805444 < baseStart_5805444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805457 : List Nat := [1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 4]
def baseStart_5805457 : Nat := 118140960795 + 5805457 * 2 ^ 59
def prefixEnd_5805457 : Nat := 4983230072969 + 3 ^ 40 * 5805457 * 2
def baseEnd_5805457 : Nat := 2980989860008997856488695

theorem tailTrace_5805457 : CollatzResearch.WordTrace tailWord_5805457 prefixEnd_5805457 2980989860008997856488695 := by
  unfold tailWord_5805457
  simp only [CollatzResearch.WordTrace]
  refine ⟨211742412128828256963910625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141161608085885504642607083 211742412128828256963910625)
  ·
    refine ⟨158806809096621192722932969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211742412128828256963910625 158806809096621192722932969)
    ·
      refine ⟨119105106822465894542199727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158806809096621192722932969 119105106822465894542199727)
      ·
        refine ⟨178657660233698841813299591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119105106822465894542199727 178657660233698841813299591)
        ·
          refine ⟨267986490350548262719949387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178657660233698841813299591 267986490350548262719949387)
          ·
            refine ⟨401979735525822394079924081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267986490350548262719949387 401979735525822394079924081)
            ·
              refine ⟨301484801644366795559943061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 401979735525822394079924081 301484801644366795559943061)
              ·
                refine ⟨14132100077079693541872331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 301484801644366795559943061 14132100077079693541872331)
                ·
                  refine ⟨21198150115619540312808497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14132100077079693541872331 21198150115619540312808497)
                  ·
                    refine ⟨15898612586714655234606373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21198150115619540312808497 15898612586714655234606373)
                    ·
                      refine ⟨2980989860008997856488695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15898612586714655234606373 2980989860008997856488695)
                      ·
                        rfl

theorem cell23_5805457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 4].length) (baseStart_5805457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805457 prefixEnd_5805457 := by exact prefixLift 5805457
  have htrace : WordTrace (prefixWord ++ tailWord_5805457) baseStart_5805457 baseEnd_5805457 := by
    simpa [prefixWord, tailWord_5805457, baseEnd_5805457] using wordTrace_append hprefix tailTrace_5805457
  have hstable : (prefixWord ++ tailWord_5805457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805457).length < 2 ^ (prefixWord ++ tailWord_5805457).sum := by decide
  have hdescent : baseEnd_5805457 < baseStart_5805457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805471 : List Nat := [1, 1, 2, 5, 1, 3, 2, 2, 2, 4]
def baseStart_5805471 : Nat := 118140960795 + 5805471 * 2 ^ 59
def prefixEnd_5805471 : Nat := 4983230072969 + 3 ^ 40 * 5805471 * 2
def baseEnd_5805471 : Nat := 993665682912720267237877

theorem tailTrace_5805471 : CollatzResearch.WordTrace tailWord_5805471 prefixEnd_5805471 993665682912720267237877 := by
  unfold tailWord_5805471
  simp only [CollatzResearch.WordTrace]
  refine ⟨211742922750777537354920267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141161948500518358236613511 211742922750777537354920267)
  ·
    refine ⟨317614384126166306032380401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211742922750777537354920267 317614384126166306032380401)
    ·
      refine ⟨238210788094624729524285301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317614384126166306032380401 238210788094624729524285301)
      ·
        refine ⟨22332261383871068392901747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 238210788094624729524285301 22332261383871068392901747)
        ·
          refine ⟨33498392075806602589352621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22332261383871068392901747 33498392075806602589352621)
          ·
            refine ⟨12561897028427475971007233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33498392075806602589352621 12561897028427475971007233)
            ·
              refine ⟨9421422771320606978255425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12561897028427475971007233 9421422771320606978255425)
              ·
                refine ⟨7066067078490455233691569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9421422771320606978255425 7066067078490455233691569)
                ·
                  refine ⟨5299550308867841425268677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7066067078490455233691569 5299550308867841425268677)
                  ·
                    refine ⟨993665682912720267237877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5299550308867841425268677 993665682912720267237877)
                    ·
                      rfl

theorem cell23_5805471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 2, 2, 4].length) (baseStart_5805471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805471 prefixEnd_5805471 := by exact prefixLift 5805471
  have htrace : WordTrace (prefixWord ++ tailWord_5805471) baseStart_5805471 baseEnd_5805471 := by
    simpa [prefixWord, tailWord_5805471, baseEnd_5805471] using wordTrace_append hprefix tailTrace_5805471
  have hstable : (prefixWord ++ tailWord_5805471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805471).length < 2 ^ (prefixWord ++ tailWord_5805471).sum := by decide
  have hdescent : baseEnd_5805471 < baseStart_5805471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805506 : List Nat := [3, 5, 2, 1, 1, 1, 2, 3, 1, 1, 3]
def baseStart_5805506 : Nat := 118140960795 + 5805506 * 2 ^ 59
def prefixEnd_5805506 : Nat := 4983230072969 + 3 ^ 40 * 5805506 * 2
def baseEnd_5805506 : Nat := 2981015020561068164775971

theorem tailTrace_5805506 : CollatzResearch.WordTrace tailWord_5805506 prefixEnd_5805506 2981015020561068164775971 := by
  unfold tailWord_5805506
  simp only [CollatzResearch.WordTrace]
  refine ⟨52936049826412684583111093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141162799537100492221629581 52936049826412684583111093)
  ·
    refine ⟨4962754671226189179666665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52936049826412684583111093 4962754671226189179666665)
    ·
      refine ⟨3722066003419641884749999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4962754671226189179666665 3722066003419641884749999)
      ·
        refine ⟨5583099005129462827124999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3722066003419641884749999 5583099005129462827124999)
        ·
          refine ⟨8374648507694194240687499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5583099005129462827124999 8374648507694194240687499)
          ·
            refine ⟨12561972761541291361031249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8374648507694194240687499 12561972761541291361031249)
            ·
              refine ⟨9421479571155968520773437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12561972761541291361031249 9421479571155968520773437)
              ·
                refine ⟨3533054839183488195290039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9421479571155968520773437 3533054839183488195290039)
                ·
                  refine ⟨5299582258775232292935059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3533054839183488195290039 5299582258775232292935059)
                  ·
                    refine ⟨7949373388162848439402589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5299582258775232292935059 7949373388162848439402589)
                    ·
                      refine ⟨2981015020561068164775971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7949373388162848439402589 2981015020561068164775971)
                      ·
                        rfl

theorem cell23_5805506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_5805506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805506 prefixEnd_5805506 := by exact prefixLift 5805506
  have htrace : WordTrace (prefixWord ++ tailWord_5805506) baseStart_5805506 baseEnd_5805506 := by
    simpa [prefixWord, tailWord_5805506, baseEnd_5805506] using wordTrace_append hprefix tailTrace_5805506
  have hstable : (prefixWord ++ tailWord_5805506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805506).length < 2 ^ (prefixWord ++ tailWord_5805506).sum := by decide
  have hdescent : baseEnd_5805506 < baseStart_5805506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805547 : List Nat := [1, 1, 1, 1, 2, 3, 2, 3, 1, 4, 4]
def baseStart_5805547 : Nat := 118140960795 + 5805547 * 2 ^ 59
def prefixEnd_5805547 : Nat := 4983230072969 + 3 ^ 40 * 5805547 * 2
def baseEnd_5805547 : Nat := 2981036073267902504363281

theorem tailTrace_5805547 : CollatzResearch.WordTrace tailWord_5805547 prefixEnd_5805547 2981036073267902504363281 := by
  unfold tailWord_5805547
  simp only [CollatzResearch.WordTrace]
  refine ⟨211745694698502202334686895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141163796465668134889791263 211745694698502202334686895)
  ·
    refine ⟨317618542047753303502030343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211745694698502202334686895 317618542047753303502030343)
    ·
      refine ⟨476427813071629955253045515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317618542047753303502030343 476427813071629955253045515)
      ·
        refine ⟨714641719607444932879568273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 476427813071629955253045515 714641719607444932879568273)
        ·
          refine ⟨535981289705583699659676205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 714641719607444932879568273 535981289705583699659676205)
          ·
            refine ⟨200992983639593887372378577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 535981289705583699659676205 200992983639593887372378577)
            ·
              refine ⟨150744737729695415529283933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200992983639593887372378577 150744737729695415529283933)
              ·
                refine ⟨56529276648635780823481475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150744737729695415529283933 56529276648635780823481475)
                ·
                  refine ⟨84793914972953671235222213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56529276648635780823481475 84793914972953671235222213)
                  ·
                    refine ⟨15898859057428813356604165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 84793914972953671235222213 15898859057428813356604165)
                    ·
                      refine ⟨2981036073267902504363281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15898859057428813356604165 2981036073267902504363281)
                      ·
                        rfl

theorem cell23_5805547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 4, 4].length) (baseStart_5805547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805547 prefixEnd_5805547 := by exact prefixLift 5805547
  have htrace : WordTrace (prefixWord ++ tailWord_5805547) baseStart_5805547 baseEnd_5805547 := by
    simpa [prefixWord, tailWord_5805547, baseEnd_5805547] using wordTrace_append hprefix tailTrace_5805547
  have hstable : (prefixWord ++ tailWord_5805547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805547).length < 2 ^ (prefixWord ++ tailWord_5805547).sum := by decide
  have hdescent : baseEnd_5805547 < baseStart_5805547 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805551 : List Nat := [1, 1, 2, 1, 4, 1, 5, 1, 1, 4, 2]
def baseStart_5805551 : Nat := 118140960795 + 5805551 * 2 ^ 59
def prefixEnd_5805551 : Nat := 4983230072969 + 3 ^ 40 * 5805551 * 2
def baseEnd_5805551 : Nat := 2981038127190520488713263

theorem tailTrace_5805551 : CollatzResearch.WordTrace tailWord_5805551 prefixEnd_5805551 2981038127190520488713263 := by
  unfold tailWord_5805551
  simp only [CollatzResearch.WordTrace]
  refine ⟨211745840590487711017832507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141163893726991807345221671 211745840590487711017832507)
  ·
    refine ⟨317618760885731566526748761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211745840590487711017832507 317618760885731566526748761)
    ·
      refine ⟨238214070664298674895061571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317618760885731566526748761 238214070664298674895061571)
      ·
        refine ⟨357321105996448012342592357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238214070664298674895061571 357321105996448012342592357)
        ·
          refine ⟨66997707374334002314236067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 357321105996448012342592357 66997707374334002314236067)
          ·
            refine ⟨100496561061501003471354101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66997707374334002314236067 100496561061501003471354101)
            ·
              refine ⟨9421552599515719075439447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 100496561061501003471354101 9421552599515719075439447)
              ·
                refine ⟨14132328899273578613159171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9421552599515719075439447 14132328899273578613159171)
                ·
                  refine ⟨21198493348910367919738757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14132328899273578613159171 21198493348910367919738757)
                  ·
                    refine ⟨3974717502920693984951017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21198493348910367919738757 3974717502920693984951017)
                    ·
                      refine ⟨2981038127190520488713263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3974717502920693984951017 2981038127190520488713263)
                      ·
                        rfl

theorem cell23_5805551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 4, 2].length) (baseStart_5805551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805551 prefixEnd_5805551 := by exact prefixLift 5805551
  have htrace : WordTrace (prefixWord ++ tailWord_5805551) baseStart_5805551 baseEnd_5805551 := by
    simpa [prefixWord, tailWord_5805551, baseEnd_5805551] using wordTrace_append hprefix tailTrace_5805551
  have hstable : (prefixWord ++ tailWord_5805551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805551).length < 2 ^ (prefixWord ++ tailWord_5805551).sum := by decide
  have hdescent : baseEnd_5805551 < baseStart_5805551 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805621 : List Nat := [1, 3, 3, 1, 1, 4, 2, 1, 2, 5]
def baseStart_5805621 : Nat := 118140960795 + 5805621 * 2 ^ 59
def prefixEnd_5805621 : Nat := 4983230072969 + 3 ^ 40 * 5805621 * 2
def baseEnd_5805621 : Nat := 993691356945445071612647

theorem tailTrace_5805621 : CollatzResearch.WordTrace tailWord_5805621 prefixEnd_5805621 993691356945445071612647 := by
  unfold tailWord_5805621
  simp only [CollatzResearch.WordTrace]
  refine ⟨211748393700234112972880717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141165595800156075315253811 211748393700234112972880717)
  ·
    refine ⟨79405647637587792364830269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211748393700234112972880717 79405647637587792364830269)
    ·
      refine ⟨29777117864095422136811351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79405647637587792364830269 29777117864095422136811351)
      ·
        refine ⟨44665676796143133205217027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29777117864095422136811351 44665676796143133205217027)
        ·
          refine ⟨66998515194214699807825541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44665676796143133205217027 66998515194214699807825541)
          ·
            refine ⟨12562221598915256213967289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66998515194214699807825541 12562221598915256213967289)
            ·
              refine ⟨9421666199186442160475467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12562221598915256213967289 9421666199186442160475467)
              ·
                refine ⟨14132499298779663240713201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9421666199186442160475467 14132499298779663240713201)
                ·
                  refine ⟨10599374474084747430534901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14132499298779663240713201 10599374474084747430534901)
                  ·
                    refine ⟨993691356945445071612647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10599374474084747430534901 993691356945445071612647)
                    ·
                      rfl

theorem cell23_5805621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_5805621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805621 prefixEnd_5805621 := by exact prefixLift 5805621
  have htrace : WordTrace (prefixWord ++ tailWord_5805621) baseStart_5805621 baseEnd_5805621 := by
    simpa [prefixWord, tailWord_5805621, baseEnd_5805621] using wordTrace_append hprefix tailTrace_5805621
  have hstable : (prefixWord ++ tailWord_5805621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805621).length < 2 ^ (prefixWord ++ tailWord_5805621).sum := by decide
  have hdescent : baseEnd_5805621 < baseStart_5805621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805678 : List Nat := [4, 1, 2, 2, 3, 1, 1, 1, 1, 4, 3]
def baseStart_5805678 : Nat := 118140960795 + 5805678 * 2 ^ 59
def prefixEnd_5805678 : Nat := 4983230072969 + 3 ^ 40 * 5805678 * 2
def baseEnd_5805678 : Nat := 2981103339233641491825179

theorem tailTrace_5805678 : CollatzResearch.WordTrace tailWord_5805678 prefixEnd_5805678 2981103339233641491825179 := by
  unfold tailWord_5805678
  simp only [CollatzResearch.WordTrace]
  refine ⟨26468809082628451463463211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141166981774018407805137125 26468809082628451463463211)
  ·
    refine ⟨39703213623942677195194817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26468809082628451463463211 39703213623942677195194817)
    ·
      refine ⟨29777410217957007896396113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39703213623942677195194817 29777410217957007896396113)
      ·
        refine ⟨22333057663467755922297085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29777410217957007896396113 22333057663467755922297085)
        ·
          refine ⟨8374896623800408470861407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22333057663467755922297085 8374896623800408470861407)
          ·
            refine ⟨12562344935700612706292111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8374896623800408470861407 12562344935700612706292111)
            ·
              refine ⟨18843517403550919059438167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12562344935700612706292111 18843517403550919059438167)
              ·
                refine ⟨28265276105326378589157251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18843517403550919059438167 28265276105326378589157251)
                ·
                  refine ⟨42397914157989567883735877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28265276105326378589157251 42397914157989567883735877)
                  ·
                    refine ⟨7949608904623043978200477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42397914157989567883735877 7949608904623043978200477)
                    ·
                      refine ⟨2981103339233641491825179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7949608904623043978200477 2981103339233641491825179)
                      ·
                        rfl

theorem cell23_5805678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_5805678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805678 prefixEnd_5805678 := by exact prefixLift 5805678
  have htrace : WordTrace (prefixWord ++ tailWord_5805678) baseStart_5805678 baseEnd_5805678 := by
    simpa [prefixWord, tailWord_5805678, baseEnd_5805678] using wordTrace_append hprefix tailTrace_5805678
  have hstable : (prefixWord ++ tailWord_5805678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805678).length < 2 ^ (prefixWord ++ tailWord_5805678).sum := by decide
  have hdescent : baseEnd_5805678 < baseStart_5805678 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805685 : List Nat := [1, 3, 4, 2, 1, 1, 1, 5, 1, 4]
def baseStart_5805685 : Nat := 118140960795 + 5805685 * 2 ^ 59
def prefixEnd_5805685 : Nat := 4983230072969 + 3 ^ 40 * 5805685 * 2
def baseEnd_5805685 : Nat := 993702311199407654812549

theorem tailTrace_5805685 : CollatzResearch.WordTrace tailWord_5805685 prefixEnd_5805685 993702311199407654812549 := by
  unfold tailWord_5805685
  simp only [CollatzResearch.WordTrace]
  refine ⟨211750727972002251903210509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141167151981334834602140339 211750727972002251903210509)
  ·
    refine ⟨79406522989500844463703941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211750727972002251903210509 79406522989500844463703941)
    ·
      refine ⟨14888723060531408336944489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79406522989500844463703941 14888723060531408336944489)
      ·
        refine ⟨11166542295398556252708367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14888723060531408336944489 11166542295398556252708367)
        ·
          refine ⟨16749813443097834379062551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11166542295398556252708367 16749813443097834379062551)
          ·
            refine ⟨25124720164646751568593827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16749813443097834379062551 25124720164646751568593827)
            ·
              refine ⟨37687080246970127352890741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25124720164646751568593827 37687080246970127352890741)
              ·
                refine ⟨3533163773153449439333507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37687080246970127352890741 3533163773153449439333507)
                ·
                  refine ⟨5299745659730174159000261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3533163773153449439333507 5299745659730174159000261)
                  ·
                    refine ⟨993702311199407654812549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5299745659730174159000261 993702311199407654812549)
                    ·
                      rfl

theorem cell23_5805685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_5805685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805685 prefixEnd_5805685 := by exact prefixLift 5805685
  have htrace : WordTrace (prefixWord ++ tailWord_5805685) baseStart_5805685 baseEnd_5805685 := by
    simpa [prefixWord, tailWord_5805685, baseEnd_5805685] using wordTrace_append hprefix tailTrace_5805685
  have hstable : (prefixWord ++ tailWord_5805685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805685).length < 2 ^ (prefixWord ++ tailWord_5805685).sum := by decide
  have hdescent : baseEnd_5805685 < baseStart_5805685 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805691 : List Nat := [1, 1, 1, 1, 1, 4, 3, 2, 5, 1, 3]
def baseStart_5805691 : Nat := 118140960795 + 5805691 * 2 ^ 59
def prefixEnd_5805691 : Nat := 4983230072969 + 3 ^ 40 * 5805691 * 2
def baseEnd_5805691 : Nat := 2981110014482149940962619

theorem tailTrace_5805691 : CollatzResearch.WordTrace tailWord_5805691 prefixEnd_5805691 2981110014482149940962619 := by
  unfold tailWord_5805691
  simp only [CollatzResearch.WordTrace]
  refine ⟨211750946809980514927928927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141167297873320343285285951 211750946809980514927928927)
  ·
    refine ⟨317626420214970772391893391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211750946809980514927928927 317626420214970772391893391)
    ·
      refine ⟨476439630322456158587840087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317626420214970772391893391 476439630322456158587840087)
      ·
        refine ⟨714659445483684237881760131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 476439630322456158587840087 714659445483684237881760131)
        ·
          refine ⟨1071989168225526356822640197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 714659445483684237881760131 1071989168225526356822640197)
          ·
            refine ⟨200997969042286191904245037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1071989168225526356822640197 200997969042286191904245037)
            ·
              refine ⟨75374238390857321964091889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 200997969042286191904245037 75374238390857321964091889)
              ·
                refine ⟨56530678793142991473068917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75374238390857321964091889 56530678793142991473068917)
                ·
                  refine ⟨5299751136857155450600211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56530678793142991473068917 5299751136857155450600211)
                  ·
                    refine ⟨7949626705285733175900317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5299751136857155450600211 7949626705285733175900317)
                    ·
                      refine ⟨2981110014482149940962619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7949626705285733175900317 2981110014482149940962619)
                      ·
                        rfl

theorem cell23_5805691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 5, 1, 3].length) (baseStart_5805691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805691 prefixEnd_5805691 := by exact prefixLift 5805691
  have htrace : WordTrace (prefixWord ++ tailWord_5805691) baseStart_5805691 baseEnd_5805691 := by
    simpa [prefixWord, tailWord_5805691, baseEnd_5805691] using wordTrace_append hprefix tailTrace_5805691
  have hstable : (prefixWord ++ tailWord_5805691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805691).length < 2 ^ (prefixWord ++ tailWord_5805691).sum := by decide
  have hdescent : baseEnd_5805691 < baseStart_5805691 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805708 : List Nat := [2, 2, 1, 2, 1, 1, 6, 1, 3, 1, 3]
def baseStart_5805708 : Nat := 118140960795 + 5805708 * 2 ^ 59
def prefixEnd_5805708 : Nat := 4983230072969 + 3 ^ 40 * 5805708 * 2
def baseEnd_5805708 : Nat := 2981118743653276374450041

theorem tailTrace_5805708 : CollatzResearch.WordTrace tailWord_5805708 prefixEnd_5805708 2981118743653276374450041 := by
  unfold tailWord_5805708
  simp only [CollatzResearch.WordTrace]
  refine ⟨105875783425459463415648889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141167711233945951220865185 105875783425459463415648889)
  ·
    refine ⟨79406837569094597561736667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105875783425459463415648889 79406837569094597561736667)
    ·
      refine ⟨119110256353641896342605001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79406837569094597561736667 119110256353641896342605001)
      ·
        refine ⟨89332692265231422256953751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119110256353641896342605001 89332692265231422256953751)
        ·
          refine ⟨133999038397847133385430627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89332692265231422256953751 133999038397847133385430627)
          ·
            refine ⟨200998557596770700078145941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133999038397847133385430627 200998557596770700078145941)
            ·
              refine ⟨9421807387348626566163091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 200998557596770700078145941 9421807387348626566163091)
              ·
                refine ⟨14132711081022939849244637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9421807387348626566163091 14132711081022939849244637)
                ·
                  refine ⟨5299766655383602443466739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14132711081022939849244637 5299766655383602443466739)
                  ·
                    refine ⟨7949649983075403665200109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5299766655383602443466739 7949649983075403665200109)
                    ·
                      refine ⟨2981118743653276374450041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7949649983075403665200109 2981118743653276374450041)
                      ·
                        rfl

theorem cell23_5805708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 3, 1, 3].length) (baseStart_5805708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805708 prefixEnd_5805708 := by exact prefixLift 5805708
  have htrace : WordTrace (prefixWord ++ tailWord_5805708) baseStart_5805708 baseEnd_5805708 := by
    simpa [prefixWord, tailWord_5805708, baseEnd_5805708] using wordTrace_append hprefix tailTrace_5805708
  have hstable : (prefixWord ++ tailWord_5805708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805708).length < 2 ^ (prefixWord ++ tailWord_5805708).sum := by decide
  have hdescent : baseEnd_5805708 < baseStart_5805708 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805728 : List Nat := [2, 1, 1, 4, 3, 2, 2, 2, 1, 5]
def baseStart_5805728 : Nat := 118140960795 + 5805728 * 2 ^ 59
def prefixEnd_5805728 : Nat := 4983230072969 + 3 ^ 40 * 5805728 * 2
def baseEnd_5805728 : Nat := 993709671088788765399983

theorem tailTrace_5805728 : CollatzResearch.WordTrace tailWord_5805728 prefixEnd_5805728 993709671088788765399983 := by
  unfold tailWord_5805728
  simp only [CollatzResearch.WordTrace]
  refine ⟨105876148155423235123512919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141168197540564313498017225 105876148155423235123512919)
  ·
    refine ⟨158814222233134852685269379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105876148155423235123512919 158814222233134852685269379)
    ·
      refine ⟨238221333349702279027904069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158814222233134852685269379 238221333349702279027904069)
      ·
        refine ⟨44666500003069177317732013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 238221333349702279027904069 44666500003069177317732013)
        ·
          refine ⟨16749937501150941494149505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44666500003069177317732013 16749937501150941494149505)
          ·
            refine ⟨12562453125863206120612129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16749937501150941494149505 12562453125863206120612129)
            ·
              refine ⟨9421839844397404590459097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12562453125863206120612129 9421839844397404590459097)
              ·
                refine ⟨7066379883298053442844323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9421839844397404590459097 7066379883298053442844323)
                ·
                  refine ⟨10599569824947080164266485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7066379883298053442844323 10599569824947080164266485)
                  ·
                    refine ⟨993709671088788765399983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10599569824947080164266485 993709671088788765399983)
                    ·
                      rfl

theorem cell23_5805728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 2, 1, 5].length) (baseStart_5805728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805728 prefixEnd_5805728 := by exact prefixLift 5805728
  have htrace : WordTrace (prefixWord ++ tailWord_5805728) baseStart_5805728 baseEnd_5805728 := by
    simpa [prefixWord, tailWord_5805728, baseEnd_5805728] using wordTrace_append hprefix tailTrace_5805728
  have hstable : (prefixWord ++ tailWord_5805728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805728).length < 2 ^ (prefixWord ++ tailWord_5805728).sum := by decide
  have hdescent : baseEnd_5805728 < baseStart_5805728 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805731 : List Nat := [1, 1, 1, 4, 1, 1, 3, 1, 2, 6, 2]
def baseStart_5805731 : Nat := 118140960795 + 5805731 * 2 ^ 59
def prefixEnd_5805731 : Nat := 4983230072969 + 3 ^ 40 * 5805731 * 2
def baseEnd_5805731 : Nat := 2981130553708329784462435

theorem tailTrace_5805731 : CollatzResearch.WordTrace tailWord_5805731 prefixEnd_5805731 2981130553708329784462435 := by
  unfold tailWord_5805731
  simp only [CollatzResearch.WordTrace]
  refine ⟨211752405729835601759385047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141168270486557067839590031 211752405729835601759385047)
  ·
    refine ⟨317628608594753402639077571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211752405729835601759385047 317628608594753402639077571)
    ·
      refine ⟨476442912892130103958616357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317628608594753402639077571 476442912892130103958616357)
      ·
        refine ⟨89333046167274394492240567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 476442912892130103958616357 89333046167274394492240567)
        ·
          refine ⟨133999569250911591738360851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89333046167274394492240567 133999569250911591738360851)
          ·
            refine ⟨200999353876367387607541277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133999569250911591738360851 200999353876367387607541277)
            ·
              refine ⟨75374757703637770352827979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 200999353876367387607541277 75374757703637770352827979)
              ·
                refine ⟨113062136555456655529241969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75374757703637770352827979 113062136555456655529241969)
                ·
                  refine ⟨84796602416592491646931477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113062136555456655529241969 84796602416592491646931477)
                  ·
                    refine ⟨3974840738277773045949913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 84796602416592491646931477 3974840738277773045949913)
                    ·
                      refine ⟨2981130553708329784462435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3974840738277773045949913 2981130553708329784462435)
                      ·
                        rfl

theorem cell23_5805731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 6, 2].length) (baseStart_5805731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805731 prefixEnd_5805731 := by exact prefixLift 5805731
  have htrace : WordTrace (prefixWord ++ tailWord_5805731) baseStart_5805731 baseEnd_5805731 := by
    simpa [prefixWord, tailWord_5805731, baseEnd_5805731] using wordTrace_append hprefix tailTrace_5805731
  have hstable : (prefixWord ++ tailWord_5805731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805731).length < 2 ^ (prefixWord ++ tailWord_5805731).sum := by decide
  have hdescent : baseEnd_5805731 < baseStart_5805731 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805736 : List Nat := [2, 1, 7, 1, 1, 2, 1, 3, 1, 4]
def baseStart_5805736 : Nat := 118140960795 + 5805736 * 2 ^ 59
def prefixEnd_5805736 : Nat := 4983230072969 + 3 ^ 40 * 5805736 * 2
def baseEnd_5805736 : Nat := 993711040370534088299971

theorem tailTrace_5805736 : CollatzResearch.WordTrace tailWord_5805736 prefixEnd_5805736 993711040370534088299971 := by
  unfold tailWord_5805736
  simp only [CollatzResearch.WordTrace]
  refine ⟨105876294047408743806658531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141168392063211658408878041 105876294047408743806658531)
  ·
    refine ⟨158814441071113115709987797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105876294047408743806658531 158814441071113115709987797)
    ·
      refine ⟨3722213462604213649452839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 158814441071113115709987797 3722213462604213649452839)
      ·
        refine ⟨5583320193906320474179259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3722213462604213649452839 5583320193906320474179259)
        ·
          refine ⟨8374980290859480711268889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5583320193906320474179259 8374980290859480711268889)
          ·
            refine ⟨6281235218144610533451667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8374980290859480711268889 6281235218144610533451667)
            ·
              refine ⟨9421852827216915800177501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6281235218144610533451667 9421852827216915800177501)
              ·
                refine ⟨3533194810206343425066563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9421852827216915800177501 3533194810206343425066563)
                ·
                  refine ⟨5299792215309515137599845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3533194810206343425066563 5299792215309515137599845)
                  ·
                    refine ⟨993711040370534088299971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5299792215309515137599845 993711040370534088299971)
                    ·
                      rfl

theorem cell23_5805736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_5805736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805736 prefixEnd_5805736 := by exact prefixLift 5805736
  have htrace : WordTrace (prefixWord ++ tailWord_5805736) baseStart_5805736 baseEnd_5805736 := by
    simpa [prefixWord, tailWord_5805736, baseEnd_5805736] using wordTrace_append hprefix tailTrace_5805736
  have hstable : (prefixWord ++ tailWord_5805736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805736).length < 2 ^ (prefixWord ++ tailWord_5805736).sum := by decide
  have hdescent : baseEnd_5805736 < baseStart_5805736 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805741 : List Nat := [1, 5, 2, 1, 1, 1, 2, 1, 3, 6]
def baseStart_5805741 : Nat := 118140960795 + 5805741 * 2 ^ 59
def prefixEnd_5805741 : Nat := 4983230072969 + 3 ^ 40 * 5805741 * 2
def baseEnd_5805741 : Nat := 993711896171624915112463

theorem tailTrace_5805741 : CollatzResearch.WordTrace tailWord_5805741 prefixEnd_5805741 993711896171624915112463 := by
  unfold tailWord_5805741
  simp only [CollatzResearch.WordTrace]
  refine ⟨211752770459799373467249077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141168513639866248978166051 211752770459799373467249077)
  ·
    refine ⟨19851822230606191262554601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 211752770459799373467249077 19851822230606191262554601)
    ·
      refine ⟨14888866672954643446915951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19851822230606191262554601 14888866672954643446915951)
      ·
        refine ⟨22333300009431965170373927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14888866672954643446915951 22333300009431965170373927)
        ·
          refine ⟨33499950014147947755560891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22333300009431965170373927 33499950014147947755560891)
          ·
            refine ⟨50249925021221921633341337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33499950014147947755560891 50249925021221921633341337)
            ·
              refine ⟨37687443765916441225006003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50249925021221921633341337 37687443765916441225006003)
              ·
                refine ⟨56531165648874661837509005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37687443765916441225006003 56531165648874661837509005)
                ·
                  refine ⟨21199187118327998189065877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56531165648874661837509005 21199187118327998189065877)
                  ·
                    refine ⟨993711896171624915112463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21199187118327998189065877 993711896171624915112463)
                    ·
                      rfl

theorem cell23_5805741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_5805741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805741 prefixEnd_5805741 := by exact prefixLift 5805741
  have htrace : WordTrace (prefixWord ++ tailWord_5805741) baseStart_5805741 baseEnd_5805741 := by
    simpa [prefixWord, tailWord_5805741, baseEnd_5805741] using wordTrace_append hprefix tailTrace_5805741
  have hstable : (prefixWord ++ tailWord_5805741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805741).length < 2 ^ (prefixWord ++ tailWord_5805741).sum := by decide
  have hdescent : baseEnd_5805741 < baseStart_5805741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805751 : List Nat := [1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 5]
def baseStart_5805751 : Nat := 118140960795 + 5805751 * 2 ^ 59
def prefixEnd_5805751 : Nat := 4983230072969 + 3 ^ 40 * 5805751 * 2
def baseEnd_5805751 : Nat := 2981140823321419706212343

theorem tailTrace_5805751 : CollatzResearch.WordTrace tailWord_5805751 prefixEnd_5805751 2981140823321419706212343 := by
  unfold tailWord_5805751
  simp only [CollatzResearch.WordTrace]
  refine ⟨211753135189763145175113107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141168756793175430116742071 211753135189763145175113107)
  ·
    refine ⟨317629702784644717762669661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211753135189763145175113107 317629702784644717762669661)
    ·
      refine ⟨119111138544241769161001123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 317629702784644717762669661 119111138544241769161001123)
      ·
        refine ⟨178666707816362653741501685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119111138544241769161001123 178666707816362653741501685)
        ·
          refine ⟨16750003857783998788265783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 178666707816362653741501685 16750003857783998788265783)
          ·
            refine ⟨25125005786675998182398675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16750003857783998788265783 25125005786675998182398675)
            ·
              refine ⟨37687508680013997273598013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25125005786675998182398675 37687508680013997273598013)
              ·
                refine ⟨14132815755005248977599255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37687508680013997273598013 14132815755005248977599255)
                ·
                  refine ⟨21199223632507873466398883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14132815755005248977599255 21199223632507873466398883)
                  ·
                    refine ⟨31798835448761810199598325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21199223632507873466398883 31798835448761810199598325)
                    ·
                      refine ⟨2981140823321419706212343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31798835448761810199598325 2981140823321419706212343)
                      ·
                        rfl

theorem cell23_5805751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 5].length) (baseStart_5805751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805751 prefixEnd_5805751 := by exact prefixLift 5805751
  have htrace : WordTrace (prefixWord ++ tailWord_5805751) baseStart_5805751 baseEnd_5805751 := by
    simpa [prefixWord, tailWord_5805751, baseEnd_5805751] using wordTrace_append hprefix tailTrace_5805751
  have hstable : (prefixWord ++ tailWord_5805751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805751).length < 2 ^ (prefixWord ++ tailWord_5805751).sum := by decide
  have hdescent : baseEnd_5805751 < baseStart_5805751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805754 : List Nat := [3, 1, 1, 1, 2, 4, 11]
def baseStart_5805754 : Nat := 118140960795 + 5805754 * 2 ^ 59
def prefixEnd_5805754 : Nat := 4983230072969 + 3 ^ 40 * 5805754 * 2
def baseEnd_5805754 : Nat := 36804226713128187586109

theorem tailTrace_5805754 : CollatzResearch.WordTrace tailWord_5805754 prefixEnd_5805754 36804226713128187586109 := by
  unfold tailWord_5805754
  simp only [CollatzResearch.WordTrace]
  refine ⟨52938311152188069171868079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141168829739168184458314877 52938311152188069171868079)
  ·
    refine ⟨79407466728282103757802119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52938311152188069171868079 79407466728282103757802119)
    ·
      refine ⟨119111200092423155636703179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79407466728282103757802119 119111200092423155636703179)
      ·
        refine ⟨178666800138634733455054769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119111200092423155636703179 178666800138634733455054769)
        ·
          refine ⟨134000100103976050091291077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178666800138634733455054769 134000100103976050091291077)
          ·
            refine ⟨25125018769495509392117077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 134000100103976050091291077 25125018769495509392117077)
            ·
              refine ⟨36804226713128187586109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 25125018769495509392117077 36804226713128187586109)
              ·
                rfl

theorem cell23_5805754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 11].length) (baseStart_5805754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805754 prefixEnd_5805754 := by exact prefixLift 5805754
  have htrace : WordTrace (prefixWord ++ tailWord_5805754) baseStart_5805754 baseEnd_5805754 := by
    simpa [prefixWord, tailWord_5805754, baseEnd_5805754] using wordTrace_append hprefix tailTrace_5805754
  have hstable : (prefixWord ++ tailWord_5805754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805754).length < 2 ^ (prefixWord ++ tailWord_5805754).sum := by decide
  have hdescent : baseEnd_5805754 < baseStart_5805754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805758 : List Nat := [4, 2, 1, 1, 2, 2, 2, 1, 4, 4]
def baseStart_5805758 : Nat := 118140960795 + 5805758 * 2 ^ 59
def prefixEnd_5805758 : Nat := 4983230072969 + 3 ^ 40 * 5805758 * 2
def baseEnd_5805758 : Nat := 993714805895333726274937

theorem tailTrace_5805758 : CollatzResearch.WordTrace tailWord_5805758 prefixEnd_5805758 993714805895333726274937 := by
  unfold tailWord_5805758
  simp only [CollatzResearch.WordTrace]
  refine ⟨26469173812592223171327241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141168927000491856913745285 26469173812592223171327241)
  ·
    refine ⟨19851880359444167378495431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26469173812592223171327241 19851880359444167378495431)
    ·
      refine ⟨29777820539166251067743147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19851880359444167378495431 29777820539166251067743147)
      ·
        refine ⟨44666730808749376601614721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29777820539166251067743147 44666730808749376601614721)
        ·
          refine ⟨33500048106562032451211041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44666730808749376601614721 33500048106562032451211041)
          ·
            refine ⟨25125036079921524338408281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33500048106562032451211041 25125036079921524338408281)
            ·
              refine ⟨18843777059941143253806211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25125036079921524338408281 18843777059941143253806211)
              ·
                refine ⟨28265665589911714880709317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18843777059941143253806211 28265665589911714880709317)
                ·
                  refine ⟨5299812298108446540132997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28265665589911714880709317 5299812298108446540132997)
                  ·
                    refine ⟨993714805895333726274937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5299812298108446540132997 993714805895333726274937)
                    ·
                      rfl

theorem cell23_5805758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_5805758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805758 prefixEnd_5805758 := by exact prefixLift 5805758
  have htrace : WordTrace (prefixWord ++ tailWord_5805758) baseStart_5805758 baseEnd_5805758 := by
    simpa [prefixWord, tailWord_5805758, baseEnd_5805758] using wordTrace_append hprefix tailTrace_5805758
  have hstable : (prefixWord ++ tailWord_5805758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805758).length < 2 ^ (prefixWord ++ tailWord_5805758).sum := by decide
  have hdescent : baseEnd_5805758 < baseStart_5805758 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805782 : List Nat := [5, 2, 1, 3, 1, 1, 1, 1, 3, 1, 4]
def baseStart_5805782 : Nat := 118140960795 + 5805782 * 2 ^ 59
def prefixEnd_5805782 : Nat := 4983230072969 + 3 ^ 40 * 5805782 * 2
def baseEnd_5805782 : Nat := 2981156741221709084924701

theorem tailTrace_5805782 : CollatzResearch.WordTrace tailWord_5805782 prefixEnd_5805782 2981156741221709084924701 := by
  unfold tailWord_5805782
  simp only [CollatzResearch.WordTrace]
  refine ⟨13234641615790677341843225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141169510568433891646327733 13234641615790677341843225)
  ·
    refine ⟨9925981211843008006382419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13234641615790677341843225 9925981211843008006382419)
    ·
      refine ⟨14888971817764512009573629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9925981211843008006382419 14888971817764512009573629)
      ·
        refine ⟨5583364431661692003590111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14888971817764512009573629 5583364431661692003590111)
        ·
          refine ⟨8375046647492538005385167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5583364431661692003590111 8375046647492538005385167)
          ·
            refine ⟨12562569971238807008077751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8375046647492538005385167 12562569971238807008077751)
            ·
              refine ⟨18843854956858210512116627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12562569971238807008077751 18843854956858210512116627)
              ·
                refine ⟨28265782435287315768174941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18843854956858210512116627 28265782435287315768174941)
                ·
                  refine ⟨10599668413232743413065603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28265782435287315768174941 10599668413232743413065603)
                  ·
                    refine ⟨15899502619849115119598405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10599668413232743413065603 15899502619849115119598405)
                    ·
                      refine ⟨2981156741221709084924701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15899502619849115119598405 2981156741221709084924701)
                      ·
                        rfl

theorem cell23_5805782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_5805782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805782 prefixEnd_5805782 := by exact prefixLift 5805782
  have htrace : WordTrace (prefixWord ++ tailWord_5805782) baseStart_5805782 baseEnd_5805782 := by
    simpa [prefixWord, tailWord_5805782, baseEnd_5805782] using wordTrace_append hprefix tailTrace_5805782
  have hstable : (prefixWord ++ tailWord_5805782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805782).length < 2 ^ (prefixWord ++ tailWord_5805782).sum := by decide
  have hdescent : baseEnd_5805782 < baseStart_5805782 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805785 : List Nat := [1, 2, 1, 2, 3, 5, 1, 2, 1, 2, 3]
def baseStart_5805785 : Nat := 118140960795 + 5805785 * 2 ^ 59
def prefixEnd_5805785 : Nat := 4983230072969 + 3 ^ 40 * 5805785 * 2
def baseEnd_5805785 : Nat := 2981158281663672573187187

theorem tailTrace_5805785 : CollatzResearch.WordTrace tailWord_5805785 prefixEnd_5805785 2981158281663672573187187 := by
  unfold tailWord_5805785
  simp only [CollatzResearch.WordTrace]
  refine ⟨211754375271639968981850809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141169583514426645987900539 211754375271639968981850809)
  ·
    refine ⟨158815781453729976736388107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211754375271639968981850809 158815781453729976736388107)
    ·
      refine ⟨238223672180594965104582161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158815781453729976736388107 238223672180594965104582161)
      ·
        refine ⟨178667754135446223828436621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238223672180594965104582161 178667754135446223828436621)
        ·
          refine ⟨67000407800792333935663733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178667754135446223828436621 67000407800792333935663733)
          ·
            refine ⟨6281288231324281306468475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67000407800792333935663733 6281288231324281306468475)
            ·
              refine ⟨9421932346986421959702713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6281288231324281306468475 9421932346986421959702713)
              ·
                refine ⟨7066449260239816469777035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9421932346986421959702713 7066449260239816469777035)
                ·
                  refine ⟨10599673890359724704665553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7066449260239816469777035 10599673890359724704665553)
                  ·
                    refine ⟨7949755417769793528499165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10599673890359724704665553 7949755417769793528499165)
                    ·
                      refine ⟨2981158281663672573187187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7949755417769793528499165 2981158281663672573187187)
                      ·
                        rfl

theorem cell23_5805785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 2, 1, 2, 3].length) (baseStart_5805785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805785 prefixEnd_5805785 := by exact prefixLift 5805785
  have htrace : WordTrace (prefixWord ++ tailWord_5805785) baseStart_5805785 baseEnd_5805785 := by
    simpa [prefixWord, tailWord_5805785, baseEnd_5805785] using wordTrace_append hprefix tailTrace_5805785
  have hstable : (prefixWord ++ tailWord_5805785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805785).length < 2 ^ (prefixWord ++ tailWord_5805785).sum := by decide
  have hdescent : baseEnd_5805785 < baseStart_5805785 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805841 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 3]
def baseStart_5805841 : Nat := 118140960795 + 5805841 * 2 ^ 59
def prefixEnd_5805841 : Nat := 4983230072969 + 3 ^ 40 * 5805841 * 2
def baseEnd_5805841 : Nat := 2981187036580324354086929

theorem tailTrace_5805841 : CollatzResearch.WordTrace tailWord_5805841 prefixEnd_5805841 2981187036580324354086929 := by
  unfold tailWord_5805841
  simp only [CollatzResearch.WordTrace]
  refine ⟨211756417759437090545889377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141170945172958060363926251 211756417759437090545889377)
  ·
    refine ⟨158817313319577817909417033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211756417759437090545889377 158817313319577817909417033)
    ·
      refine ⟨119112984989683363432062775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158817313319577817909417033 119112984989683363432062775)
      ·
        refine ⟨178669477484525045148094163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119112984989683363432062775 178669477484525045148094163)
        ·
          refine ⟨268004216226787567722141245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178669477484525045148094163 268004216226787567722141245)
          ·
            refine ⟨100501581085045337895802967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 268004216226787567722141245 100501581085045337895802967)
            ·
              refine ⟨150752371627568006843704451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100501581085045337895802967 150752371627568006843704451)
              ·
                refine ⟨226128557441352010265556677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150752371627568006843704451 226128557441352010265556677)
                ·
                  refine ⟨42399104520253501924791877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 226128557441352010265556677 42399104520253501924791877)
                  ·
                    refine ⟨7949832097547531610898477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42399104520253501924791877 7949832097547531610898477)
                    ·
                      refine ⟨2981187036580324354086929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7949832097547531610898477 2981187036580324354086929)
                      ·
                        rfl

theorem cell23_5805841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 3].length) (baseStart_5805841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805841 prefixEnd_5805841 := by exact prefixLift 5805841
  have htrace : WordTrace (prefixWord ++ tailWord_5805841) baseStart_5805841 baseEnd_5805841 := by
    simpa [prefixWord, tailWord_5805841, baseEnd_5805841] using wordTrace_append hprefix tailTrace_5805841
  have hstable : (prefixWord ++ tailWord_5805841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805841).length < 2 ^ (prefixWord ++ tailWord_5805841).sum := by decide
  have hdescent : baseEnd_5805841 < baseStart_5805841 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805842 : List Nat := [3, 2, 4, 1, 1, 1, 2, 1, 3, 3, 2]
def baseStart_5805842 : Nat := 118140960795 + 5805842 * 2 ^ 59
def prefixEnd_5805842 : Nat := 4983230072969 + 3 ^ 40 * 5805842 * 2
def baseEnd_5805842 : Nat := 2981187550060978850174425

theorem tailTrace_5805842 : CollatzResearch.WordTrace tailWord_5805842 prefixEnd_5805842 2981187550060978850174425 := by
  unfold tailWord_5805842
  simp only [CollatzResearch.WordTrace]
  refine ⟨52939113558108366929168945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141170969488288978477783853 52939113558108366929168945)
  ·
    refine ⟨39704335168581275196876709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52939113558108366929168945 39704335168581275196876709)
    ·
      refine ⟨7444562844108989099414383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39704335168581275196876709 7444562844108989099414383)
      ·
        refine ⟨11166844266163483649121575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7444562844108989099414383 11166844266163483649121575)
        ·
          refine ⟨16750266399245225473682363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11166844266163483649121575 16750266399245225473682363)
          ·
            refine ⟨25125399598867838210523545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16750266399245225473682363 25125399598867838210523545)
            ·
              refine ⟨18844049699150878657892659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25125399598867838210523545 18844049699150878657892659)
              ·
                refine ⟨28266074548726317986838989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18844049699150878657892659 28266074548726317986838989)
                ·
                  refine ⟨10599777955772369245064621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28266074548726317986838989 10599777955772369245064621)
                  ·
                    refine ⟨3974916733414638466899233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10599777955772369245064621 3974916733414638466899233)
                    ·
                      refine ⟨2981187550060978850174425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3974916733414638466899233 2981187550060978850174425)
                      ·
                        rfl

theorem cell23_5805842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_5805842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805842 prefixEnd_5805842 := by exact prefixLift 5805842
  have htrace : WordTrace (prefixWord ++ tailWord_5805842) baseStart_5805842 baseEnd_5805842 := by
    simpa [prefixWord, tailWord_5805842, baseEnd_5805842] using wordTrace_append hprefix tailTrace_5805842
  have hstable : (prefixWord ++ tailWord_5805842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805842).length < 2 ^ (prefixWord ++ tailWord_5805842).sum := by decide
  have hdescent : baseEnd_5805842 < baseStart_5805842 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805855 : List Nat := [1, 1, 2, 4, 2, 1, 2, 2, 4, 2, 2]
def baseStart_5805855 : Nat := 118140960795 + 5805855 * 2 ^ 59
def prefixEnd_5805855 : Nat := 4983230072969 + 3 ^ 40 * 5805855 * 2
def baseEnd_5805855 : Nat := 2981194225309487299311865

theorem tailTrace_5805855 : CollatzResearch.WordTrace tailWord_5805855 prefixEnd_5805855 2981194225309487299311865 := by
  unfold tailWord_5805855
  simp only [CollatzResearch.WordTrace]
  refine ⟨211756928381386370936899019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141171285587590913957932679 211756928381386370936899019)
  ·
    refine ⟨317635392572079556405348529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211756928381386370936899019 317635392572079556405348529)
    ·
      refine ⟨238226544429059667304011397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317635392572079556405348529 238226544429059667304011397)
      ·
        refine ⟨44667477080448687619502137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 238226544429059667304011397 44667477080448687619502137)
        ·
          refine ⟨33500607810336515714626603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44667477080448687619502137 33500607810336515714626603)
          ·
            refine ⟨50250911715504773571939905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33500607810336515714626603 50250911715504773571939905)
            ·
              refine ⟨37688183786628580178954929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50250911715504773571939905 37688183786628580178954929)
              ·
                refine ⟨28266137839971435134216197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37688183786628580178954929 28266137839971435134216197)
                ·
                  refine ⟨5299900844994644087665537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28266137839971435134216197 5299900844994644087665537)
                  ·
                    refine ⟨3974925633745983065749153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5299900844994644087665537 3974925633745983065749153)
                    ·
                      refine ⟨2981194225309487299311865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3974925633745983065749153 2981194225309487299311865)
                      ·
                        rfl

theorem cell23_5805855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 4, 2, 2].length) (baseStart_5805855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805855 prefixEnd_5805855 := by exact prefixLift 5805855
  have htrace : WordTrace (prefixWord ++ tailWord_5805855) baseStart_5805855 baseEnd_5805855 := by
    simpa [prefixWord, tailWord_5805855, baseEnd_5805855] using wordTrace_append hprefix tailTrace_5805855
  have hstable : (prefixWord ++ tailWord_5805855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805855).length < 2 ^ (prefixWord ++ tailWord_5805855).sum := by decide
  have hdescent : baseEnd_5805855 < baseStart_5805855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805871 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 3, 5, 3]
def baseStart_5805871 : Nat := 118140960795 + 5805871 * 2 ^ 59
def prefixEnd_5805871 : Nat := 4983230072969 + 3 ^ 40 * 5805871 * 2
def baseEnd_5805871 : Nat := 2981202440999959236711791

theorem tailTrace_5805871 : CollatzResearch.WordTrace tailWord_5805871 prefixEnd_5805871 2981202440999959236711791 := by
  unfold tailWord_5805871
  simp only [CollatzResearch.WordTrace]
  refine ⟨211757511949328405669481467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141171674632885603779654311 211757511949328405669481467)
  ·
    refine ⟨317636267923992608504222201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211757511949328405669481467 317636267923992608504222201)
    ·
      refine ⟨238227200942994456378166651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317636267923992608504222201 238227200942994456378166651)
      ·
        refine ⟨357340801414491684567249977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238227200942994456378166651 357340801414491684567249977)
        ·
          refine ⟨268005601060868763425437483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 357340801414491684567249977 268005601060868763425437483)
          ·
            refine ⟨402008401591303145138156225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268005601060868763425437483 402008401591303145138156225)
            ·
              refine ⟨301506301193477358853617169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 402008401591303145138156225 301506301193477358853617169)
              ·
                refine ⟨226129725895108019140212877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 301506301193477358853617169 226129725895108019140212877)
                ·
                  refine ⟨84798647210665507177579829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 226129725895108019140212877 84798647210665507177579829)
                  ·
                    refine ⟨7949873175999891297898109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 84798647210665507177579829 7949873175999891297898109)
                    ·
                      refine ⟨2981202440999959236711791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7949873175999891297898109 2981202440999959236711791)
                      ·
                        rfl

theorem cell23_5805871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 5, 3].length) (baseStart_5805871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805871 prefixEnd_5805871 := by exact prefixLift 5805871
  have htrace : WordTrace (prefixWord ++ tailWord_5805871) baseStart_5805871 baseEnd_5805871 := by
    simpa [prefixWord, tailWord_5805871, baseEnd_5805871] using wordTrace_append hprefix tailTrace_5805871
  have hstable : (prefixWord ++ tailWord_5805871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805871).length < 2 ^ (prefixWord ++ tailWord_5805871).sum := by decide
  have hdescent : baseEnd_5805871 < baseStart_5805871 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805891 : List Nat := [1, 1, 1, 3, 1, 5, 1, 2, 1, 7]
def baseStart_5805891 : Nat := 118140960795 + 5805891 * 2 ^ 59
def prefixEnd_5805891 : Nat := 4983230072969 + 3 ^ 40 * 5805891 * 2
def baseEnd_5805891 : Nat := 993737570204349719487233

theorem tailTrace_5805891 : CollatzResearch.WordTrace tailWord_5805891 prefixEnd_5805891 993737570204349719487233 := by
  unfold tailWord_5805891
  simp only [CollatzResearch.WordTrace]
  refine ⟨211758241409255949085209527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141172160939503966056806351 211758241409255949085209527)
  ·
    refine ⟨317637362113883923627814291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211758241409255949085209527 317637362113883923627814291)
    ·
      refine ⟨476456043170825885441721437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317637362113883923627814291 476456043170825885441721437)
      ·
        refine ⟨178671016189059707040645539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 476456043170825885441721437 178671016189059707040645539)
        ·
          refine ⟨268006524283589560560968309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178671016189059707040645539 268006524283589560560968309)
          ·
            refine ⟨25125611651586521302590779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 268006524283589560560968309 25125611651586521302590779)
            ·
              refine ⟨37688417477379781953886169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25125611651586521302590779 37688417477379781953886169)
              ·
                refine ⟨28266313108034836465414627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37688417477379781953886169 28266313108034836465414627)
                ·
                  refine ⟨42399469662052254698121941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28266313108034836465414627 42399469662052254698121941)
                  ·
                    refine ⟨993737570204349719487233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42399469662052254698121941 993737570204349719487233)
                    ·
                      rfl

theorem cell23_5805891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 7].length) (baseStart_5805891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805891 prefixEnd_5805891 := by exact prefixLift 5805891
  have htrace : WordTrace (prefixWord ++ tailWord_5805891) baseStart_5805891 baseEnd_5805891 := by
    simpa [prefixWord, tailWord_5805891, baseEnd_5805891] using wordTrace_append hprefix tailTrace_5805891
  have hstable : (prefixWord ++ tailWord_5805891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805891).length < 2 ^ (prefixWord ++ tailWord_5805891).sum := by decide
  have hdescent : baseEnd_5805891 < baseStart_5805891 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805908 : List Nat := [2, 4, 1, 1, 3, 1, 2, 1, 1, 7]
def baseStart_5805908 : Nat := 118140960795 + 5805908 * 2 ^ 59
def prefixEnd_5805908 : Nat := 4983230072969 + 3 ^ 40 * 5805908 * 2
def baseEnd_5805908 : Nat := 993740479928058530649707

theorem tailTrace_5805908 : CollatzResearch.WordTrace tailWord_5805908 prefixEnd_5805908 993740479928058530649707 := by
  unfold tailWord_5805908
  simp only [CollatzResearch.WordTrace]
  refine ⟨105879430725097180494289189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141172574300129573992385585 105879430725097180494289189)
  ·
    refine ⟨19852393260955721342679223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105879430725097180494289189 19852393260955721342679223)
    ·
      refine ⟨29778589891433582014018835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19852393260955721342679223 29778589891433582014018835)
      ·
        refine ⟨44667884837150373021028253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29778589891433582014018835 44667884837150373021028253)
        ·
          refine ⟨16750456813931389882885595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44667884837150373021028253 16750456813931389882885595)
          ·
            refine ⟨25125685220897084824328393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16750456813931389882885595 25125685220897084824328393)
            ·
              refine ⟨18844263915672813618246295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25125685220897084824328393 18844263915672813618246295)
              ·
                refine ⟨28266395873509220427369443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18844263915672813618246295 28266395873509220427369443)
                ·
                  refine ⟨42399593810263830641054165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28266395873509220427369443 42399593810263830641054165)
                  ·
                    refine ⟨993740479928058530649707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42399593810263830641054165 993740479928058530649707)
                    ·
                      rfl

theorem cell23_5805908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_5805908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805908 prefixEnd_5805908 := by exact prefixLift 5805908
  have htrace : WordTrace (prefixWord ++ tailWord_5805908) baseStart_5805908 baseEnd_5805908 := by
    simpa [prefixWord, tailWord_5805908, baseEnd_5805908] using wordTrace_append hprefix tailTrace_5805908
  have hstable : (prefixWord ++ tailWord_5805908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805908).length < 2 ^ (prefixWord ++ tailWord_5805908).sum := by decide
  have hdescent : baseEnd_5805908 < baseStart_5805908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5805962 : List Nat := [3, 1, 2, 4, 2, 1, 2, 1, 2, 1, 4]
def baseStart_5805962 : Nat := 118140960795 + 5805962 * 2 ^ 59
def prefixEnd_5805962 : Nat := 4983230072969 + 3 ^ 40 * 5805962 * 2
def baseEnd_5805962 : Nat := 2981249167739518380673873

theorem tailTrace_5805962 : CollatzResearch.WordTrace tailWord_5805962 prefixEnd_5805962 2981249167739518380673873 := by
  unfold tailWord_5805962
  simp only [CollatzResearch.WordTrace]
  refine ⟨52940207747999682052761035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141173887327999152140696093 52940207747999682052761035)
  ·
    refine ⟨79410311621999523079141553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52940207747999682052761035 79410311621999523079141553)
    ·
      refine ⟨59557733716499642309356165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79410311621999523079141553 59557733716499642309356165)
      ·
        refine ⟨11167075071843682933004281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59557733716499642309356165 11167075071843682933004281)
        ·
          refine ⟨8375306303882762199753211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11167075071843682933004281 8375306303882762199753211)
          ·
            refine ⟨12562959455824143299629817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8375306303882762199753211 12562959455824143299629817)
            ·
              refine ⟨9422219591868107474722363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12562959455824143299629817 9422219591868107474722363)
              ·
                refine ⟨14133329387802161212083545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9422219591868107474722363 14133329387802161212083545)
                ·
                  refine ⟨10599997040851620909062659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14133329387802161212083545 10599997040851620909062659)
                  ·
                    refine ⟨15899995561277431363593989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10599997040851620909062659 15899995561277431363593989)
                    ·
                      refine ⟨2981249167739518380673873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15899995561277431363593989 2981249167739518380673873)
                      ·
                        rfl

theorem cell23_5805962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_5805962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5805962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5805962 prefixEnd_5805962 := by exact prefixLift 5805962
  have htrace : WordTrace (prefixWord ++ tailWord_5805962) baseStart_5805962 baseEnd_5805962 := by
    simpa [prefixWord, tailWord_5805962, baseEnd_5805962] using wordTrace_append hprefix tailTrace_5805962
  have hstable : (prefixWord ++ tailWord_5805962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5805962).length < 2 ^ (prefixWord ++ tailWord_5805962).sum := by decide
  have hdescent : baseEnd_5805962 < baseStart_5805962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5805962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5806048 : List Nat := [2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 4]
def baseStart_5806048 : Nat := 118140960795 + 5806048 * 2 ^ 59
def prefixEnd_5806048 : Nat := 4983230072969 + 3 ^ 40 * 5806048 * 2
def baseEnd_5806048 : Nat := 2981293327075805044198477

theorem tailTrace_5806048 : CollatzResearch.WordTrace tailWord_5806048 prefixEnd_5806048 2981293327075805044198477 := by
  unfold tailWord_5806048
  simp only [CollatzResearch.WordTrace]
  refine ⟨105881983834843582449337399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141175978446458109932449865 105881983834843582449337399)
  ·
    refine ⟨158822975752265373674006099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105881983834843582449337399 158822975752265373674006099)
    ·
      refine ⟨238234463628398060511009149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158822975752265373674006099 238234463628398060511009149)
      ·
        refine ⟨89337923860649272691628431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238234463628398060511009149 89337923860649272691628431)
        ·
          refine ⟨134006885790973909037442647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89337923860649272691628431 134006885790973909037442647)
          ·
            refine ⟨201010328686460863556163971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134006885790973909037442647 201010328686460863556163971)
            ·
              refine ⟨301515493029691295334245957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201010328686460863556163971 301515493029691295334245957)
              ·
                refine ⟨56534154943067117875171117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 301515493029691295334245957 56534154943067117875171117)
                ·
                  refine ⟨21200308103650169203189169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56534154943067117875171117 21200308103650169203189169)
                  ·
                    refine ⟨15900231077737626902391877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21200308103650169203189169 15900231077737626902391877)
                    ·
                      refine ⟨2981293327075805044198477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15900231077737626902391877 2981293327075805044198477)
                      ·
                        rfl

theorem cell23_5806048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_5806048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806048 prefixEnd_5806048 := by exact prefixLift 5806048
  have htrace : WordTrace (prefixWord ++ tailWord_5806048) baseStart_5806048 baseEnd_5806048 := by
    simpa [prefixWord, tailWord_5806048, baseEnd_5806048] using wordTrace_append hprefix tailTrace_5806048
  have hstable : (prefixWord ++ tailWord_5806048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806048).length < 2 ^ (prefixWord ++ tailWord_5806048).sum := by decide
  have hdescent : baseEnd_5806048 < baseStart_5806048 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5806058 : List Nat := [3, 1, 3, 1, 2, 1, 2, 10]
def baseStart_5806058 : Nat := 118140960795 + 5806058 * 2 ^ 59
def prefixEnd_5806058 : Nat := 4983230072969 + 3 ^ 40 * 5806058 * 2
def baseEnd_5806058 : Nat := 110418461551198148336053

theorem tailTrace_5806058 : CollatzResearch.WordTrace tailWord_5806058 prefixEnd_5806058 110418461551198148336053 := by
  unfold tailWord_5806058
  simp only [CollatzResearch.WordTrace]
  refine ⟨52941083099912734151634707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141176221599767291071025885 52941083099912734151634707)
  ·
    refine ⟨79411624649869101227452061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52941083099912734151634707 79411624649869101227452061)
    ·
      refine ⟨29779359243700912960294523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79411624649869101227452061 29779359243700912960294523)
      ·
        refine ⟨44669038865551369440441785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29779359243700912960294523 44669038865551369440441785)
        ·
          refine ⟨33501779149163527080331339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44669038865551369440441785 33501779149163527080331339)
          ·
            refine ⟨50252668723745290620497009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33501779149163527080331339 50252668723745290620497009)
            ·
              refine ⟨37689501542808967965372757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50252668723745290620497009 37689501542808967965372757)
              ·
                refine ⟨110418461551198148336053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 37689501542808967965372757 110418461551198148336053)
                ·
                  rfl

theorem cell23_5806058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 10].length) (baseStart_5806058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806058 prefixEnd_5806058 := by exact prefixLift 5806058
  have htrace : WordTrace (prefixWord ++ tailWord_5806058) baseStart_5806058 baseEnd_5806058 := by
    simpa [prefixWord, tailWord_5806058, baseEnd_5806058] using wordTrace_append hprefix tailTrace_5806058
  have hstable : (prefixWord ++ tailWord_5806058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806058).length < 2 ^ (prefixWord ++ tailWord_5806058).sum := by decide
  have hdescent : baseEnd_5806058 < baseStart_5806058 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5806062 : List Nat := [4, 1, 2, 1, 3, 3, 1, 1, 1, 6]
def baseStart_5806062 : Nat := 118140960795 + 5806062 * 2 ^ 59
def prefixEnd_5806062 : Nat := 4983230072969 + 3 ^ 40 * 5806062 * 2
def baseEnd_5806062 : Nat := 993766838601655996474471

theorem tailTrace_5806062 : CollatzResearch.WordTrace tailWord_5806062 prefixEnd_5806062 993766838601655996474471 := by
  unfold tailWord_5806062
  simp only [CollatzResearch.WordTrace]
  refine ⟨26470559786454555661210555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141176318861090963526456293 26470559786454555661210555)
  ·
    refine ⟨39705839679681833491815833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26470559786454555661210555 39705839679681833491815833)
    ·
      refine ⟨29779379759761375118861875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39705839679681833491815833 29779379759761375118861875)
      ·
        refine ⟨44669069639642062678292813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29779379759761375118861875 44669069639642062678292813)
        ·
          refine ⟨16750901114865773504359805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44669069639642062678292813 16750901114865773504359805)
          ·
            refine ⟨6281587918074665064134927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16750901114865773504359805 6281587918074665064134927)
            ·
              refine ⟨9422381877111997596202391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6281587918074665064134927 9422381877111997596202391)
              ·
                refine ⟨14133572815667996394303587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9422381877111997596202391 14133572815667996394303587)
                ·
                  refine ⟨21200359223501994591455381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14133572815667996394303587 21200359223501994591455381)
                  ·
                    refine ⟨993766838601655996474471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21200359223501994591455381 993766838601655996474471)
                    ·
                      rfl

theorem cell23_5806062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_5806062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806062 prefixEnd_5806062 := by exact prefixLift 5806062
  have htrace : WordTrace (prefixWord ++ tailWord_5806062) baseStart_5806062 baseEnd_5806062 := by
    simpa [prefixWord, tailWord_5806062, baseEnd_5806062] using wordTrace_append hprefix tailTrace_5806062
  have hstable : (prefixWord ++ tailWord_5806062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806062).length < 2 ^ (prefixWord ++ tailWord_5806062).sum := by decide
  have hdescent : baseEnd_5806062 < baseStart_5806062 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5806065 : List Nat := [1, 2, 2, 2, 5, 1, 1, 1, 1, 1, 6]
def baseStart_5806065 : Nat := 118140960795 + 5806065 * 2 ^ 59
def prefixEnd_5806065 : Nat := 4983230072969 + 3 ^ 40 * 5806065 * 2
def baseEnd_5806065 : Nat := 2981302056246931477685899

theorem tailTrace_5806065 : CollatzResearch.WordTrace tailWord_5806065 prefixEnd_5806065 2981302056246931477685899 := by
  unfold tailWord_5806065
  simp only [CollatzResearch.WordTrace]
  refine ⟨211764587710625576802043649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141176391807083717868029099 211764587710625576802043649)
  ·
    refine ⟨158823440782969182601532737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211764587710625576802043649 158823440782969182601532737)
    ·
      refine ⟨119117580587226886951149553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158823440782969182601532737 119117580587226886951149553)
      ·
        refine ⟨89338185440420165213362165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119117580587226886951149553 89338185440420165213362165)
        ·
          refine ⟨8375454885039390488752703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89338185440420165213362165 8375454885039390488752703)
          ·
            refine ⟨12563182327559085733129055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8375454885039390488752703 12563182327559085733129055)
            ·
              refine ⟨18844773491338628599693583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12563182327559085733129055 18844773491338628599693583)
              ·
                refine ⟨28267160237007942899540375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18844773491338628599693583 28267160237007942899540375)
                ·
                  refine ⟨42400740355511914349310563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28267160237007942899540375 42400740355511914349310563)
                  ·
                    refine ⟨63601110533267871523965845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42400740355511914349310563 63601110533267871523965845)
                    ·
                      refine ⟨2981302056246931477685899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63601110533267871523965845 2981302056246931477685899)
                      ·
                        rfl

theorem cell23_5806065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 1, 6].length) (baseStart_5806065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806065 prefixEnd_5806065 := by exact prefixLift 5806065
  have htrace : WordTrace (prefixWord ++ tailWord_5806065) baseStart_5806065 baseEnd_5806065 := by
    simpa [prefixWord, tailWord_5806065, baseEnd_5806065] using wordTrace_append hprefix tailTrace_5806065
  have hstable : (prefixWord ++ tailWord_5806065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806065).length < 2 ^ (prefixWord ++ tailWord_5806065).sum := by decide
  have hdescent : baseEnd_5806065 < baseStart_5806065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5806103 : List Nat := [1, 1, 3, 5, 3, 1, 1, 1, 3, 2, 2]
def baseStart_5806103 : Nat := 118140960795 + 5806103 * 2 ^ 59
def prefixEnd_5806103 : Nat := 4983230072969 + 3 ^ 40 * 5806103 * 2
def baseEnd_5806103 : Nat := 2981321568511802329010725

theorem tailTrace_5806103 : CollatzResearch.WordTrace tailWord_5806103 prefixEnd_5806103 2981321568511802329010725 := by
  unfold tailWord_5806103
  simp only [CollatzResearch.WordTrace]
  refine ⟨211765973684487909291926963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141177315789658606194617975 211765973684487909291926963)
  ·
    refine ⟨317648960526731863937890445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211765973684487909291926963 317648960526731863937890445)
    ·
      refine ⟨119118360197524448976708917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 317648960526731863937890445 119118360197524448976708917)
      ·
        refine ⟨11167346268517917091566461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 119118360197524448976708917 11167346268517917091566461)
        ·
          refine ⟨4187754850694218909337423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11167346268517917091566461 4187754850694218909337423)
          ·
            refine ⟨6281632276041328364006135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4187754850694218909337423 6281632276041328364006135)
            ·
              refine ⟨9422448414061992546009203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6281632276041328364006135 9422448414061992546009203)
              ·
                refine ⟨14133672621092988819013805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9422448414061992546009203 14133672621092988819013805)
                ·
                  refine ⟨5300127232909870807130177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14133672621092988819013805 5300127232909870807130177)
                  ·
                    refine ⟨3975095424682403105347633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5300127232909870807130177 3975095424682403105347633)
                    ·
                      refine ⟨2981321568511802329010725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3975095424682403105347633 2981321568511802329010725)
                      ·
                        rfl

theorem cell23_5806103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_5806103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806103 prefixEnd_5806103 := by exact prefixLift 5806103
  have htrace : WordTrace (prefixWord ++ tailWord_5806103) baseStart_5806103 baseEnd_5806103 := by
    simpa [prefixWord, tailWord_5806103, baseEnd_5806103] using wordTrace_append hprefix tailTrace_5806103
  have hstable : (prefixWord ++ tailWord_5806103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806103).length < 2 ^ (prefixWord ++ tailWord_5806103).sum := by decide
  have hdescent : baseEnd_5806103 < baseStart_5806103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5806129 : List Nat := [1, 2, 2, 3, 1, 3, 3, 2, 1, 3, 2]
def baseStart_5806129 : Nat := 118140960795 + 5806129 * 2 ^ 59
def prefixEnd_5806129 : Nat := 4983230072969 + 3 ^ 40 * 5806129 * 2
def baseEnd_5806129 : Nat := 2981334919008819227285605

theorem tailTrace_5806129 : CollatzResearch.WordTrace tailWord_5806129 prefixEnd_5806129 2981334919008819227285605 := by
  unfold tailWord_5806129
  simp only [CollatzResearch.WordTrace]
  refine ⟨211766921982393715732373441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141177947988262477154915627 211766921982393715732373441)
  ·
    refine ⟨158825191486795286799280081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211766921982393715732373441 158825191486795286799280081)
    ·
      refine ⟨119118893615096465099460061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158825191486795286799280081 119118893615096465099460061)
      ·
        refine ⟨44669585105661174412297523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119118893615096465099460061 44669585105661174412297523)
        ·
          refine ⟨67004377658491761618446285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44669585105661174412297523 67004377658491761618446285)
          ·
            refine ⟨25126641621934410606917357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67004377658491761618446285 25126641621934410606917357)
            ·
              refine ⟨9422490608225403977594009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25126641621934410606917357 9422490608225403977594009)
              ·
                refine ⟨7066867956169052983195507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9422490608225403977594009 7066867956169052983195507)
                ·
                  refine ⟨10600301934253579474793261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7066867956169052983195507 10600301934253579474793261)
                  ·
                    refine ⟨3975113225345092303047473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10600301934253579474793261 3975113225345092303047473)
                    ·
                      refine ⟨2981334919008819227285605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3975113225345092303047473 2981334919008819227285605)
                      ·
                        rfl

theorem cell23_5806129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 2, 1, 3, 2].length) (baseStart_5806129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806129 prefixEnd_5806129 := by exact prefixLift 5806129
  have htrace : WordTrace (prefixWord ++ tailWord_5806129) baseStart_5806129 baseEnd_5806129 := by
    simpa [prefixWord, tailWord_5806129, baseEnd_5806129] using wordTrace_append hprefix tailTrace_5806129
  have hstable : (prefixWord ++ tailWord_5806129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806129).length < 2 ^ (prefixWord ++ tailWord_5806129).sum := by decide
  have hdescent : baseEnd_5806129 < baseStart_5806129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5806172 : List Nat := [2, 2, 4, 1, 1, 3, 1, 1, 2, 2, 4]
def baseStart_5806172 : Nat := 118140960795 + 5806172 * 2 ^ 59
def prefixEnd_5806172 : Nat := 4983230072969 + 3 ^ 40 * 5806172 * 2
def baseEnd_5806172 : Nat := 2981356998676962559047907

theorem tailTrace_5806172 : CollatzResearch.WordTrace tailWord_5806172 prefixEnd_5806172 2981356998676962559047907 := by
  unfold tailWord_5806172
  simp only [CollatzResearch.WordTrace]
  refine ⟨105884245160618967038094385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141178993547491956050792513 105884245160618967038094385)
  ·
    refine ⟨79413183870464225278570789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105884245160618967038094385 79413183870464225278570789)
    ·
      refine ⟨14889971975712042239732023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79413183870464225278570789 14889971975712042239732023)
      ·
        refine ⟨22334957963568063359598035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14889971975712042239732023 22334957963568063359598035)
        ·
          refine ⟨33502436945352095039397053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22334957963568063359598035 33502436945352095039397053)
          ·
            refine ⟨12563413854507035639773895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33502436945352095039397053 12563413854507035639773895)
            ·
              refine ⟨18845120781760553459660843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12563413854507035639773895 18845120781760553459660843)
              ·
                refine ⟨28267681172640830189491265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18845120781760553459660843 28267681172640830189491265)
                ·
                  refine ⟨21200760879480622642118449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28267681172640830189491265 21200760879480622642118449)
                  ·
                    refine ⟨15900570659610466981588837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21200760879480622642118449 15900570659610466981588837)
                    ·
                      refine ⟨2981356998676962559047907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15900570659610466981588837 2981356998676962559047907)
                      ·
                        rfl

theorem cell23_5806172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_5806172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806172 prefixEnd_5806172 := by exact prefixLift 5806172
  have htrace : WordTrace (prefixWord ++ tailWord_5806172) baseStart_5806172 baseEnd_5806172 := by
    simpa [prefixWord, tailWord_5806172, baseEnd_5806172] using wordTrace_append hprefix tailTrace_5806172
  have hstable : (prefixWord ++ tailWord_5806172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806172).length < 2 ^ (prefixWord ++ tailWord_5806172).sum := by decide
  have hdescent : baseEnd_5806172 < baseStart_5806172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5806235 : List Nat := [1, 1, 1, 1, 1, 1, 2, 5, 3, 4, 3]
def baseStart_5806235 : Nat := 118140960795 + 5806235 * 2 ^ 59
def prefixEnd_5806235 : Nat := 4983230072969 + 3 ^ 40 * 5806235 * 2
def baseEnd_5806235 : Nat := 2981389347958195812560117

theorem tailTrace_5806235 : CollatzResearch.WordTrace tailWord_5806235 prefixEnd_5806235 2981389347958195812560117 := by
  unfold tailWord_5806235
  simp only [CollatzResearch.WordTrace]
  refine ⟨211770788120009695835732159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141180525413339797223821439 211770788120009695835732159)
  ·
    refine ⟨317656182180014543753598239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211770788120009695835732159 317656182180014543753598239)
    ·
      refine ⟨476484273270021815630397359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317656182180014543753598239 476484273270021815630397359)
      ·
        refine ⟨714726409905032723445596039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 476484273270021815630397359 714726409905032723445596039)
        ·
          refine ⟨1072089614857549085168394059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 714726409905032723445596039 1072089614857549085168394059)
          ·
            refine ⟨1608134422286323627752591089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1072089614857549085168394059 1608134422286323627752591089)
            ·
              refine ⟨1206100816714742720814443317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1608134422286323627752591089 1206100816714742720814443317)
              ·
                refine ⟨113071951567007130076354061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1206100816714742720814443317 113071951567007130076354061)
                ·
                  refine ⟨42401981837627673778632773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113071951567007130076354061 42401981837627673778632773)
                  ·
                    refine ⟨7950371594555188833493645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42401981837627673778632773 7950371594555188833493645)
                    ·
                      refine ⟨2981389347958195812560117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7950371594555188833493645 2981389347958195812560117)
                      ·
                        rfl

theorem cell23_5806235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 4, 3].length) (baseStart_5806235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806235 prefixEnd_5806235 := by exact prefixLift 5806235
  have htrace : WordTrace (prefixWord ++ tailWord_5806235) baseStart_5806235 baseEnd_5806235 := by
    simpa [prefixWord, tailWord_5806235, baseEnd_5806235] using wordTrace_append hprefix tailTrace_5806235
  have hstable : (prefixWord ++ tailWord_5806235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806235).length < 2 ^ (prefixWord ++ tailWord_5806235).sum := by decide
  have hdescent : baseEnd_5806235 < baseStart_5806235 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5806245 : List Nat := [1, 3, 1, 2, 1, 3, 1, 1, 2, 4, 4]
def baseStart_5806245 : Nat := 118140960795 + 5806245 * 2 ^ 59
def prefixEnd_5806245 : Nat := 4983230072969 + 3 ^ 40 * 5806245 * 2
def baseEnd_5806245 : Nat := 2981394482764740773435071

theorem tailTrace_5806245 : CollatzResearch.WordTrace tailWord_5806245 prefixEnd_5806245 2981394482764740773435071 := by
  unfold tailWord_5806245
  simp only [CollatzResearch.WordTrace]
  refine ⟨211771152849973467543596189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141180768566648978362397459 211771152849973467543596189)
  ·
    refine ⟨79414182318740050328848571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211771152849973467543596189 79414182318740050328848571)
    ·
      refine ⟨119121273478110075493272857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79414182318740050328848571 119121273478110075493272857)
      ·
        refine ⟨89340955108582556619954643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119121273478110075493272857 89340955108582556619954643)
        ·
          refine ⟨134011432662873834929931965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89340955108582556619954643 134011432662873834929931965)
          ·
            refine ⟨50254287248577688098724487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134011432662873834929931965 50254287248577688098724487)
            ·
              refine ⟨75381430872866532148086731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50254287248577688098724487 75381430872866532148086731)
              ·
                refine ⟨113072146309299798222130097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75381430872866532148086731 113072146309299798222130097)
                ·
                  refine ⟨84804109731974848666597573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113072146309299798222130097 84804109731974848666597573)
                  ·
                    refine ⟨15900770574745284124987045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 84804109731974848666597573 15900770574745284124987045)
                    ·
                      refine ⟨2981394482764740773435071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15900770574745284124987045 2981394482764740773435071)
                      ·
                        rfl

theorem cell23_5806245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_5806245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806245 prefixEnd_5806245 := by exact prefixLift 5806245
  have htrace : WordTrace (prefixWord ++ tailWord_5806245) baseStart_5806245 baseEnd_5806245 := by
    simpa [prefixWord, tailWord_5806245, baseEnd_5806245] using wordTrace_append hprefix tailTrace_5806245
  have hstable : (prefixWord ++ tailWord_5806245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806245).length < 2 ^ (prefixWord ++ tailWord_5806245).sum := by decide
  have hdescent : baseEnd_5806245 < baseStart_5806245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5806276 : List Nat := [2, 3, 3, 1, 2, 3, 1, 1, 3, 4]
def baseStart_5806276 : Nat := 118140960795 + 5806276 * 2 ^ 59
def prefixEnd_5806276 : Nat := 4983230072969 + 3 ^ 40 * 5806276 * 2
def baseEnd_5806276 : Nat := 993803466888343384049143

theorem tailTrace_5806276 : CollatzResearch.WordTrace tailWord_5806276 prefixEnd_5806276 993803466888343384049143 := by
  unfold tailWord_5806276
  simp only [CollatzResearch.WordTrace]
  refine ⟨105886141756430579918987341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141181522341907439891983121 105886141756430579918987341)
  ·
    refine ⟨39707303158661467469620253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105886141756430579918987341 39707303158661467469620253)
    ·
      refine ⟨14890238684498050301107595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39707303158661467469620253 14890238684498050301107595)
      ·
        refine ⟨22335358026747075451661393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14890238684498050301107595 22335358026747075451661393)
        ·
          refine ⟨16751518520060306588746045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22335358026747075451661393 16751518520060306588746045)
          ·
            refine ⟨6281819445022614970779767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16751518520060306588746045 6281819445022614970779767)
            ·
              refine ⟨9422729167533922456169651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6281819445022614970779767 9422729167533922456169651)
              ·
                refine ⟨14134093751300883684254477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9422729167533922456169651 14134093751300883684254477)
                ·
                  refine ⟨5300285156737831381595429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14134093751300883684254477 5300285156737831381595429)
                  ·
                    refine ⟨993803466888343384049143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5300285156737831381595429 993803466888343384049143)
                    ·
                      rfl

theorem cell23_5806276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_5806276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806276 prefixEnd_5806276 := by exact prefixLift 5806276
  have htrace : WordTrace (prefixWord ++ tailWord_5806276) baseStart_5806276 baseEnd_5806276 := by
    simpa [prefixWord, tailWord_5806276, baseEnd_5806276] using wordTrace_append hprefix tailTrace_5806276
  have hstable : (prefixWord ++ tailWord_5806276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806276).length < 2 ^ (prefixWord ++ tailWord_5806276).sum := by decide
  have hdescent : baseEnd_5806276 < baseStart_5806276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5806316 : List Nat := [2, 2, 1, 1, 2, 3, 2, 5, 1, 1, 3]
def baseStart_5806316 : Nat := 118140960795 + 5806316 * 2 ^ 59
def prefixEnd_5806316 : Nat := 4983230072969 + 3 ^ 40 * 5806316 * 2
def baseEnd_5806316 : Nat := 2981430939891209995647245

theorem tailTrace_5806316 : CollatzResearch.WordTrace tailWord_5806316 prefixEnd_5806316 2981430939891209995647245 := by
  unfold tailWord_5806316
  simp only [CollatzResearch.WordTrace]
  refine ⟨105886871216358123334715401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141182494955144164446287201 105886871216358123334715401)
  ·
    refine ⟨79415153412268592501036551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105886871216358123334715401 79415153412268592501036551)
    ·
      refine ⟨119122730118402888751554827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79415153412268592501036551 119122730118402888751554827)
      ·
        refine ⟨178684095177604333127332241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119122730118402888751554827 178684095177604333127332241)
        ·
          refine ⟨134013071383203249845499181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178684095177604333127332241 134013071383203249845499181)
          ·
            refine ⟨50254901768701218692062193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134013071383203249845499181 50254901768701218692062193)
            ·
              refine ⟨37691176326525914019046645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50254901768701218692062193 37691176326525914019046645)
              ·
                refine ⟨3533547780611804439285623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37691176326525914019046645 3533547780611804439285623)
                ·
                  refine ⟨5300321670917706658928435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3533547780611804439285623 5300321670917706658928435)
                  ·
                    refine ⟨7950482506376559988392653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5300321670917706658928435 7950482506376559988392653)
                    ·
                      refine ⟨2981430939891209995647245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7950482506376559988392653 2981430939891209995647245)
                      ·
                        rfl

theorem cell23_5806316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 5, 1, 1, 3].length) (baseStart_5806316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806316 prefixEnd_5806316 := by exact prefixLift 5806316
  have htrace : WordTrace (prefixWord ++ tailWord_5806316) baseStart_5806316 baseEnd_5806316 := by
    simpa [prefixWord, tailWord_5806316, baseEnd_5806316] using wordTrace_append hprefix tailTrace_5806316
  have hstable : (prefixWord ++ tailWord_5806316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806316).length < 2 ^ (prefixWord ++ tailWord_5806316).sum := by decide
  have hdescent : baseEnd_5806316 < baseStart_5806316 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5806326 : List Nat := [5, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2]
def baseStart_5806326 : Nat := 118140960795 + 5806326 * 2 ^ 59
def prefixEnd_5806326 : Nat := 4983230072969 + 3 ^ 40 * 5806326 * 2
def baseEnd_5806326 : Nat := 2981436074697754956522199

theorem tailTrace_5806326 : CollatzResearch.WordTrace tailWord_5806326 prefixEnd_5806326 2981436074697754956522199 := by
  unfold tailWord_5806326
  simp only [CollatzResearch.WordTrace]
  refine ⟨13235881697667501148580927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141182738108453345584863221 13235881697667501148580927)
  ·
    refine ⟨19853822546501251722871391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13235881697667501148580927 19853822546501251722871391)
    ·
      refine ⟨29780733819751877584307087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19853822546501251722871391 29780733819751877584307087)
      ·
        refine ⟨44671100729627816376460631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29780733819751877584307087 44671100729627816376460631)
        ·
          refine ⟨67006651094441724564690947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44671100729627816376460631 67006651094441724564690947)
          ·
            refine ⟨100509976641662586847036421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67006651094441724564690947 100509976641662586847036421)
            ·
              refine ⟨18845620620311735033819329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100509976641662586847036421 18845620620311735033819329)
              ·
                refine ⟨14134215465233801275364497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18845620620311735033819329 14134215465233801275364497)
                ·
                  refine ⟨10600661598925350956523373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14134215465233801275364497 10600661598925350956523373)
                  ·
                    refine ⟨3975248099597006608696265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10600661598925350956523373 3975248099597006608696265)
                    ·
                      refine ⟨2981436074697754956522199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3975248099597006608696265 2981436074697754956522199)
                      ·
                        rfl

theorem cell23_5806326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2].length) (baseStart_5806326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806326 prefixEnd_5806326 := by exact prefixLift 5806326
  have htrace : WordTrace (prefixWord ++ tailWord_5806326) baseStart_5806326 baseEnd_5806326 := by
    simpa [prefixWord, tailWord_5806326, baseEnd_5806326] using wordTrace_append hprefix tailTrace_5806326
  have hstable : (prefixWord ++ tailWord_5806326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806326).length < 2 ^ (prefixWord ++ tailWord_5806326).sum := by decide
  have hdescent : baseEnd_5806326 < baseStart_5806326 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5806355 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 7]
def baseStart_5806355 : Nat := 118140960795 + 5806355 * 2 ^ 59
def prefixEnd_5806355 : Nat := 4983230072969 + 3 ^ 40 * 5806355 * 2
def baseEnd_5806355 : Nat := 2981450965636735343059565

theorem tailTrace_5806355 : CollatzResearch.WordTrace tailWord_5806355 prefixEnd_5806355 2981450965636735343059565 := by
  unfold tailWord_5806355
  simp only [CollatzResearch.WordTrace]
  refine ⟨211775164879574956330100519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141183443253049970886733679 211775164879574956330100519)
  ·
    refine ⟨317662747319362434495150779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211775164879574956330100519 317662747319362434495150779)
    ·
      refine ⟨476494120979043651742726169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317662747319362434495150779 476494120979043651742726169)
      ·
        refine ⟨357370590734282738807044627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 476494120979043651742726169 357370590734282738807044627)
        ·
          refine ⟨536055886101424108210566941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357370590734282738807044627 536055886101424108210566941)
          ·
            refine ⟨201020957288034040578962603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 536055886101424108210566941 201020957288034040578962603)
            ·
              refine ⟨301531435932051060868443905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201020957288034040578962603 301531435932051060868443905)
              ·
                refine ⟨226148576949038295651332929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 301531435932051060868443905 226148576949038295651332929)
                ·
                  refine ⟨169611432711778721738499697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 226148576949038295651332929 169611432711778721738499697)
                  ·
                    refine ⟨127208574533834041303874773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 169611432711778721738499697 127208574533834041303874773)
                    ·
                      refine ⟨2981450965636735343059565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 127208574533834041303874773 2981450965636735343059565)
                      ·
                        rfl

theorem cell23_5806355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 7].length) (baseStart_5806355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806355 prefixEnd_5806355 := by exact prefixLift 5806355
  have htrace : WordTrace (prefixWord ++ tailWord_5806355) baseStart_5806355 baseEnd_5806355 := by
    simpa [prefixWord, tailWord_5806355, baseEnd_5806355] using wordTrace_append hprefix tailTrace_5806355
  have hstable : (prefixWord ++ tailWord_5806355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806355).length < 2 ^ (prefixWord ++ tailWord_5806355).sum := by decide
  have hdescent : baseEnd_5806355 < baseStart_5806355 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5806359 : List Nat := [1, 1, 3, 4, 1, 2, 2, 1, 3, 2, 3]
def baseStart_5806359 : Nat := 118140960795 + 5806359 * 2 ^ 59
def prefixEnd_5806359 : Nat := 4983230072969 + 3 ^ 40 * 5806359 * 2
def baseEnd_5806359 : Nat := 2981453019559353327409547

theorem tailTrace_5806359 : CollatzResearch.WordTrace tailWord_5806359 prefixEnd_5806359 2981453019559353327409547 := by
  unfold tailWord_5806359
  simp only [CollatzResearch.WordTrace]
  refine ⟨211775310771560465013246131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141183540514373643342164087 211775310771560465013246131)
  ·
    refine ⟨317662966157340697519869197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211775310771560465013246131 317662966157340697519869197)
    ·
      refine ⟨119123612309002761569950949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 317662966157340697519869197 119123612309002761569950949)
      ·
        refine ⟨22335677307938017794365803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119123612309002761569950949 22335677307938017794365803)
        ·
          refine ⟨33503515961907026691548705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22335677307938017794365803 33503515961907026691548705)
          ·
            refine ⟨25127636971430270018661529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33503515961907026691548705 25127636971430270018661529)
            ·
              refine ⟨18845727728572702513996147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25127636971430270018661529 18845727728572702513996147)
              ·
                refine ⟨28268591592859053770994221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18845727728572702513996147 28268591592859053770994221)
                ·
                  refine ⟨10600721847322145164122833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28268591592859053770994221 10600721847322145164122833)
                  ·
                    refine ⟨7950541385491608873092125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10600721847322145164122833 7950541385491608873092125)
                    ·
                      refine ⟨2981453019559353327409547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7950541385491608873092125 2981453019559353327409547)
                      ·
                        rfl

theorem cell23_5806359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_5806359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806359 prefixEnd_5806359 := by exact prefixLift 5806359
  have htrace : WordTrace (prefixWord ++ tailWord_5806359) baseStart_5806359 baseEnd_5806359 := by
    simpa [prefixWord, tailWord_5806359, baseEnd_5806359] using wordTrace_append hprefix tailTrace_5806359
  have hstable : (prefixWord ++ tailWord_5806359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806359).length < 2 ^ (prefixWord ++ tailWord_5806359).sum := by decide
  have hdescent : baseEnd_5806359 < baseStart_5806359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5806366 : List Nat := [4, 3, 2, 1, 1, 1, 2, 2, 1, 6]
def baseStart_5806366 : Nat := 118140960795 + 5806366 * 2 ^ 59
def prefixEnd_5806366 : Nat := 4983230072969 + 3 ^ 40 * 5806366 * 2
def baseEnd_5806366 : Nat := 993818871307978266674005

theorem tailTrace_5806366 : CollatzResearch.WordTrace tailWord_5806366 prefixEnd_5806366 993818871307978266674005 := by
  unfold tailWord_5806366
  simp only [CollatzResearch.WordTrace]
  refine ⟨26471945760316888151093869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141183710721690070139167301 26471945760316888151093869)
  ·
    refine ⟨9926979660118833056660201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26471945760316888151093869 9926979660118833056660201)
    ·
      refine ⟨7445234745089124792495151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9926979660118833056660201 7445234745089124792495151)
      ·
        refine ⟨11167852117633687188742727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7445234745089124792495151 11167852117633687188742727)
        ·
          refine ⟨16751778176450530783114091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11167852117633687188742727 16751778176450530783114091)
          ·
            refine ⟨25127667264675796174671137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16751778176450530783114091 25127667264675796174671137)
            ·
              refine ⟨18845750448506847131003353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25127667264675796174671137 18845750448506847131003353)
              ·
                refine ⟨14134312836380135348252515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18845750448506847131003353 14134312836380135348252515)
                ·
                  refine ⟨21201469254570203022378773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14134312836380135348252515 21201469254570203022378773)
                  ·
                    refine ⟨993818871307978266674005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21201469254570203022378773 993818871307978266674005)
                    ·
                      rfl

theorem cell23_5806366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_5806366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806366 prefixEnd_5806366 := by exact prefixLift 5806366
  have htrace : WordTrace (prefixWord ++ tailWord_5806366) baseStart_5806366 baseEnd_5806366 := by
    simpa [prefixWord, tailWord_5806366, baseEnd_5806366] using wordTrace_append hprefix tailTrace_5806366
  have hstable : (prefixWord ++ tailWord_5806366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806366).length < 2 ^ (prefixWord ++ tailWord_5806366).sum := by decide
  have hdescent : baseEnd_5806366 < baseStart_5806366 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5806373 : List Nat := [1, 3, 1, 2, 5, 2, 2, 1, 1, 1, 4]
def baseStart_5806373 : Nat := 118140960795 + 5806373 * 2 ^ 59
def prefixEnd_5806373 : Nat := 4983230072969 + 3 ^ 40 * 5806373 * 2
def baseEnd_5806373 : Nat := 2981460208288516272634483

theorem tailTrace_5806373 : CollatzResearch.WordTrace tailWord_5806373 prefixEnd_5806373 2981460208288516272634483 := by
  unfold tailWord_5806373
  simp only [CollatzResearch.WordTrace]
  refine ⟨211775821393509745404255773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141183880929006496936170515 211775821393509745404255773)
  ·
    refine ⟨79415933022566154526595915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211775821393509745404255773 79415933022566154526595915)
    ·
      refine ⟨119123899533849231789893873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79415933022566154526595915 119123899533849231789893873)
      ·
        refine ⟨89342924650386923842420405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119123899533849231789893873 89342924650386923842420405)
        ·
          refine ⟨8375899185973774110226913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89342924650386923842420405 8375899185973774110226913)
          ·
            refine ⟨6281924389480330582670185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8375899185973774110226913 6281924389480330582670185)
            ·
              refine ⟨4711443292110247937002639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6281924389480330582670185 4711443292110247937002639)
              ·
                refine ⟨7067164938165371905503959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4711443292110247937002639 7067164938165371905503959)
                ·
                  refine ⟨10600747407248057858255939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7067164938165371905503959 10600747407248057858255939)
                  ·
                    refine ⟨15901121110872086787383909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10600747407248057858255939 15901121110872086787383909)
                    ·
                      refine ⟨2981460208288516272634483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15901121110872086787383909 2981460208288516272634483)
                      ·
                        rfl

theorem cell23_5806373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 1, 1, 1, 4].length) (baseStart_5806373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806373 prefixEnd_5806373 := by exact prefixLift 5806373
  have htrace : WordTrace (prefixWord ++ tailWord_5806373) baseStart_5806373 baseEnd_5806373 := by
    simpa [prefixWord, tailWord_5806373, baseEnd_5806373] using wordTrace_append hprefix tailTrace_5806373
  have hstable : (prefixWord ++ tailWord_5806373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806373).length < 2 ^ (prefixWord ++ tailWord_5806373).sum := by decide
  have hdescent : baseEnd_5806373 < baseStart_5806373 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5806416 : List Nat := [2, 1, 1, 1, 1, 6, 1, 4, 1, 3, 2]
def baseStart_5806416 : Nat := 118140960795 + 5806416 * 2 ^ 59
def prefixEnd_5806416 : Nat := 4983230072969 + 3 ^ 40 * 5806416 * 2
def baseEnd_5806416 : Nat := 2981482287956659604396785

theorem tailTrace_5806416 : CollatzResearch.WordTrace tailWord_5806416 prefixEnd_5806416 2981482287956659604396785 := by
  unfold tailWord_5806416
  simp only [CollatzResearch.WordTrace]
  refine ⟨105888694866176981874035551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141184926488235975832047401 105888694866176981874035551)
  ·
    refine ⟨158833042299265472811053327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105888694866176981874035551 158833042299265472811053327)
    ·
      refine ⟨238249563448898209216579991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158833042299265472811053327 238249563448898209216579991)
      ·
        refine ⟨357374345173347313824869987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238249563448898209216579991 357374345173347313824869987)
        ·
          refine ⟨536061517760020970737304981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357374345173347313824869987 536061517760020970737304981)
          ·
            refine ⟨25127883645000983003311171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 536061517760020970737304981 25127883645000983003311171)
            ·
              refine ⟨37691825467501474504966757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25127883645000983003311171 37691825467501474504966757)
              ·
                refine ⟨7067217275156526469681267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37691825467501474504966757 7067217275156526469681267)
                ·
                  refine ⟨10600825912734789704521901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7067217275156526469681267 10600825912734789704521901)
                  ·
                    refine ⟨3975309717275546139195713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10600825912734789704521901 3975309717275546139195713)
                    ·
                      refine ⟨2981482287956659604396785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3975309717275546139195713 2981482287956659604396785)
                      ·
                        rfl

theorem cell23_5806416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 4, 1, 3, 2].length) (baseStart_5806416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806416 prefixEnd_5806416 := by exact prefixLift 5806416
  have htrace : WordTrace (prefixWord ++ tailWord_5806416) baseStart_5806416 baseEnd_5806416 := by
    simpa [prefixWord, tailWord_5806416, baseEnd_5806416] using wordTrace_append hprefix tailTrace_5806416
  have hstable : (prefixWord ++ tailWord_5806416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806416).length < 2 ^ (prefixWord ++ tailWord_5806416).sum := by decide
  have hdescent : baseEnd_5806416 < baseStart_5806416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5806430 : List Nat := [4, 4, 2, 1, 1, 2, 9]
def baseStart_5806430 : Nat := 118140960795 + 5806430 * 2 ^ 59
def prefixEnd_5806430 : Nat := 4983230072969 + 3 ^ 40 * 5806430 * 2
def baseEnd_5806430 : Nat := 36808512057849661106441

theorem tailTrace_5806430 : CollatzResearch.WordTrace tailWord_5806430 prefixEnd_5806430 36808512057849661106441 := by
  unfold tailWord_5806430
  simp only [CollatzResearch.WordTrace]
  refine ⟨26472237544287905517385093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141185266902868829426053829 26472237544287905517385093)
  ·
    refine ⟨4963544539553982284509705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26472237544287905517385093 4963544539553982284509705)
    ·
      refine ⟨3722658404665486713382279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4963544539553982284509705 3722658404665486713382279)
      ·
        refine ⟨5583987606998230070073419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3722658404665486713382279 5583987606998230070073419)
        ·
          refine ⟨8375981410497345105110129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5583987606998230070073419 8375981410497345105110129)
          ·
            refine ⟨6281986057873008828832597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8375981410497345105110129 6281986057873008828832597)
            ·
              refine ⟨36808512057849661106441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6281986057873008828832597 36808512057849661106441)
              ·
                rfl

theorem cell23_5806430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 9].length) (baseStart_5806430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806430 prefixEnd_5806430 := by exact prefixLift 5806430
  have htrace : WordTrace (prefixWord ++ tailWord_5806430) baseStart_5806430 baseEnd_5806430 := by
    simpa [prefixWord, tailWord_5806430, baseEnd_5806430] using wordTrace_append hprefix tailTrace_5806430
  have hstable : (prefixWord ++ tailWord_5806430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806430).length < 2 ^ (prefixWord ++ tailWord_5806430).sum := by decide
  have hdescent : baseEnd_5806430 < baseStart_5806430 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5806497 : List Nat := [1, 2, 3, 5, 1, 1, 2, 2, 2, 2, 2]
def baseStart_5806497 : Nat := 118140960795 + 5806497 * 2 ^ 59
def prefixEnd_5806497 : Nat := 4983230072969 + 3 ^ 40 * 5806497 * 2
def baseEnd_5806497 : Nat := 2981523879889673787483913

theorem tailTrace_5806497 : CollatzResearch.WordTrace tailWord_5806497 prefixEnd_5806497 2981523879889673787483913 := by
  unfold tailWord_5806497
  simp only [CollatzResearch.WordTrace]
  refine ⟨211780344045060514581769745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141186896030040343054513163 211780344045060514581769745)
  ·
    refine ⟨158835258033795385936327309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211780344045060514581769745 158835258033795385936327309)
    ·
      refine ⟨59563221762673269726122741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158835258033795385936327309 59563221762673269726122741)
      ·
        refine ⟨5584052040250619036824007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59563221762673269726122741 5584052040250619036824007)
        ·
          refine ⟨8376078060375928555236011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5584052040250619036824007 8376078060375928555236011)
          ·
            refine ⟨12564117090563892832854017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8376078060375928555236011 12564117090563892832854017)
            ·
              refine ⟨9423087817922919624640513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12564117090563892832854017 9423087817922919624640513)
              ·
                refine ⟨7067315863442189718480385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9423087817922919624640513 7067315863442189718480385)
                ·
                  refine ⟨5300486897581642288860289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7067315863442189718480385 5300486897581642288860289)
                  ·
                    refine ⟨3975365173186231716645217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5300486897581642288860289 3975365173186231716645217)
                    ·
                      refine ⟨2981523879889673787483913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3975365173186231716645217 2981523879889673787483913)
                      ·
                        rfl

theorem cell23_5806497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_5806497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806497 prefixEnd_5806497 := by exact prefixLift 5806497
  have htrace : WordTrace (prefixWord ++ tailWord_5806497) baseStart_5806497 baseEnd_5806497 := by
    simpa [prefixWord, tailWord_5806497, baseEnd_5806497] using wordTrace_append hprefix tailTrace_5806497
  have hstable : (prefixWord ++ tailWord_5806497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806497).length < 2 ^ (prefixWord ++ tailWord_5806497).sum := by decide
  have hdescent : baseEnd_5806497 < baseStart_5806497 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5806499 : List Nat := [1, 1, 1, 4, 1, 4, 2, 2, 2, 5]
def baseStart_5806499 : Nat := 118140960795 + 5806499 * 2 ^ 59
def prefixEnd_5806499 : Nat := 4983230072969 + 3 ^ 40 * 5806499 * 2
def baseEnd_5806499 : Nat := 993841635616994259886301

theorem tailTrace_5806499 : CollatzResearch.WordTrace tailWord_5806499 prefixEnd_5806499 993841635616994259886301 := by
  unfold tailWord_5806499
  simp only [CollatzResearch.WordTrace]
  refine ⟨211780416991053268923342551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141186944660702179282228367 211780416991053268923342551)
  ·
    refine ⟨317670625486579903385013827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211780416991053268923342551 317670625486579903385013827)
    ·
      refine ⟨476505938229869855077520741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317670625486579903385013827 476505938229869855077520741)
      ·
        refine ⟨89344863418100597827035139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 476505938229869855077520741 89344863418100597827035139)
        ·
          refine ⟨134017295127150896740552709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89344863418100597827035139 134017295127150896740552709)
          ·
            refine ⟨25128242836340793138853633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 134017295127150896740552709 25128242836340793138853633)
            ·
              refine ⟨18846182127255594854140225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25128242836340793138853633 18846182127255594854140225)
              ·
                refine ⟨14134636595441696140605169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18846182127255594854140225 14134636595441696140605169)
                ·
                  refine ⟨10600977446581272105453877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14134636595441696140605169 10600977446581272105453877)
                  ·
                    refine ⟨993841635616994259886301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10600977446581272105453877 993841635616994259886301)
                    ·
                      rfl

theorem cell23_5806499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 2, 5].length) (baseStart_5806499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806499 prefixEnd_5806499 := by exact prefixLift 5806499
  have htrace : WordTrace (prefixWord ++ tailWord_5806499) baseStart_5806499 baseEnd_5806499 := by
    simpa [prefixWord, tailWord_5806499, baseEnd_5806499] using wordTrace_append hprefix tailTrace_5806499
  have hstable : (prefixWord ++ tailWord_5806499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806499).length < 2 ^ (prefixWord ++ tailWord_5806499).sum := by decide
  have hdescent : baseEnd_5806499 < baseStart_5806499 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5806503 : List Nat := [1, 1, 6, 1, 1, 2, 4, 2, 5]
def baseStart_5806503 : Nat := 118140960795 + 5806503 * 2 ^ 59
def prefixEnd_5806503 : Nat := 4983230072969 + 3 ^ 40 * 5806503 * 2
def baseEnd_5806503 : Nat := 331280773419288973778765

theorem tailTrace_5806503 : CollatzResearch.WordTrace tailWord_5806503 prefixEnd_5806503 331280773419288973778765 := by
  unfold tailWord_5806503
  simp only [CollatzResearch.WordTrace]
  refine ⟨211780562883038777606488163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141187041922025851737658775 211780562883038777606488163)
  ·
    refine ⟨317670844324558166409732245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211780562883038777606488163 317670844324558166409732245)
    ·
      refine ⟨14890820827713664050456199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 317670844324558166409732245 14890820827713664050456199)
      ·
        refine ⟨22336231241570496075684299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14890820827713664050456199 22336231241570496075684299)
        ·
          refine ⟨33504346862355744113526449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22336231241570496075684299 33504346862355744113526449)
          ·
            refine ⟨25128260146766808085144837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33504346862355744113526449 25128260146766808085144837)
            ·
              refine ⟨4711548777518776515964657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25128260146766808085144837 4711548777518776515964657)
              ·
                refine ⟨3533661583139082386973493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4711548777518776515964657 3533661583139082386973493)
                ·
                  refine ⟨331280773419288973778765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3533661583139082386973493 331280773419288973778765)
                  ·
                    rfl

theorem cell23_5806503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 2, 5].length) (baseStart_5806503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806503 prefixEnd_5806503 := by exact prefixLift 5806503
  have htrace : WordTrace (prefixWord ++ tailWord_5806503) baseStart_5806503 baseEnd_5806503 := by
    simpa [prefixWord, tailWord_5806503, baseEnd_5806503] using wordTrace_append hprefix tailTrace_5806503
  have hstable : (prefixWord ++ tailWord_5806503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806503).length < 2 ^ (prefixWord ++ tailWord_5806503).sum := by decide
  have hdescent : baseEnd_5806503 < baseStart_5806503 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5806536 : List Nat := [2, 1, 3, 1, 3, 2, 3, 1, 2, 1, 4]
def baseStart_5806536 : Nat := 118140960795 + 5806536 * 2 ^ 59
def prefixEnd_5806536 : Nat := 4983230072969 + 3 ^ 40 * 5806536 * 2
def baseEnd_5806536 : Nat := 2981543905635199134896233

theorem tailTrace_5806536 : CollatzResearch.WordTrace tailWord_5806536 prefixEnd_5806536 2981543905635199134896233 := by
  unfold tailWord_5806536
  simp only [CollatzResearch.WordTrace]
  refine ⟨105890883245959612121219731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141187844327946149494959641 105890883245959612121219731)
  ·
    refine ⟨158836324868939418181829597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105890883245959612121219731 158836324868939418181829597)
    ·
      refine ⟨59563621825852281818186099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158836324868939418181829597 59563621825852281818186099)
      ·
        refine ⟨89345432738778422727279149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59563621825852281818186099 89345432738778422727279149)
        ·
          refine ⟨33504537277041908522729681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89345432738778422727279149 33504537277041908522729681)
          ·
            refine ⟨25128402957781431392047261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33504537277041908522729681 25128402957781431392047261)
            ·
              refine ⟨9423151109168036772017723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25128402957781431392047261 9423151109168036772017723)
              ·
                refine ⟨14134726663752055158026585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9423151109168036772017723 14134726663752055158026585)
                ·
                  refine ⟨10601044997814041368519939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14134726663752055158026585 10601044997814041368519939)
                  ·
                    refine ⟨15901567496721062052779909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10601044997814041368519939 15901567496721062052779909)
                    ·
                      refine ⟨2981543905635199134896233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15901567496721062052779909 2981543905635199134896233)
                      ·
                        rfl

theorem cell23_5806536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 2, 1, 4].length) (baseStart_5806536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806536 prefixEnd_5806536 := by exact prefixLift 5806536
  have htrace : WordTrace (prefixWord ++ tailWord_5806536) baseStart_5806536 baseEnd_5806536 := by
    simpa [prefixWord, tailWord_5806536, baseEnd_5806536] using wordTrace_append hprefix tailTrace_5806536
  have hstable : (prefixWord ++ tailWord_5806536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806536).length < 2 ^ (prefixWord ++ tailWord_5806536).sum := by decide
  have hdescent : baseEnd_5806536 < baseStart_5806536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5806549 : List Nat := [1, 3, 2, 3, 1, 2, 1, 1, 2, 1, 6]
def baseStart_5806549 : Nat := 118140960795 + 5806549 * 2 ^ 59
def prefixEnd_5806549 : Nat := 4983230072969 + 3 ^ 40 * 5806549 * 2
def baseEnd_5806549 : Nat := 2981550580883707584033673

theorem tailTrace_5806549 : CollatzResearch.WordTrace tailWord_5806549 prefixEnd_5806549 2981550580883707584033673 := by
  unfold tailWord_5806549
  simp only [CollatzResearch.WordTrace]
  refine ⟨211782240640872127462662701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141188160427248084975108467 211782240640872127462662701)
  ·
    refine ⟨79418340240327047798498513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211782240640872127462662701 79418340240327047798498513)
    ·
      refine ⟨59563755180245285848873885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79418340240327047798498513 59563755180245285848873885)
      ·
        refine ⟨22336408192591982193327707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59563755180245285848873885 22336408192591982193327707)
        ·
          refine ⟨33504612288887973289991561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22336408192591982193327707 33504612288887973289991561)
          ·
            refine ⟨25128459216665979967493671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33504612288887973289991561 25128459216665979967493671)
            ·
              refine ⟨37692688824998969951240507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25128459216665979967493671 37692688824998969951240507)
              ·
                refine ⟨56539033237498454926860761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37692688824998969951240507 56539033237498454926860761)
                ·
                  refine ⟨42404274928123841195145571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56539033237498454926860761 42404274928123841195145571)
                  ·
                    refine ⟨63606412392185761792718357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42404274928123841195145571 63606412392185761792718357)
                    ·
                      refine ⟨2981550580883707584033673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63606412392185761792718357 2981550580883707584033673)
                      ·
                        rfl

theorem cell23_5806549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_5806549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806549 prefixEnd_5806549 := by exact prefixLift 5806549
  have htrace : WordTrace (prefixWord ++ tailWord_5806549) baseStart_5806549 baseEnd_5806549 := by
    simpa [prefixWord, tailWord_5806549, baseEnd_5806549] using wordTrace_append hprefix tailTrace_5806549
  have hstable : (prefixWord ++ tailWord_5806549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806549).length < 2 ^ (prefixWord ++ tailWord_5806549).sum := by decide
  have hdescent : baseEnd_5806549 < baseStart_5806549 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5806559 : List Nat := [1, 1, 2, 3, 3, 3, 1, 1, 8]
def baseStart_5806559 : Nat := 118140960795 + 5806559 * 2 ^ 59
def prefixEnd_5806559 : Nat := 4983230072969 + 3 ^ 40 * 5806559 * 2
def baseEnd_5806559 : Nat := 331283968410028060545403

theorem tailTrace_5806559 : CollatzResearch.WordTrace tailWord_5806559 prefixEnd_5806559 331283968410028060545403 := by
  unfold tailWord_5806559
  simp only [CollatzResearch.WordTrace]
  refine ⟨211782605370835899170526731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141188403580557266113684487 211782605370835899170526731)
  ·
    refine ⟨317673908056253848755790097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211782605370835899170526731 317673908056253848755790097)
    ·
      refine ⟨238255431042190386566842573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317673908056253848755790097 238255431042190386566842573)
      ·
        refine ⟨89345786640821394962565965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238255431042190386566842573 89345786640821394962565965)
        ·
          refine ⟨33504669990308023110962237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89345786640821394962565965 33504669990308023110962237)
          ·
            refine ⟨12564251246365508666610839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33504669990308023110962237 12564251246365508666610839)
            ·
              refine ⟨18846376869548262999916259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12564251246365508666610839 18846376869548262999916259)
              ·
                refine ⟨28269565304322394499874389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18846376869548262999916259 28269565304322394499874389)
                ·
                  refine ⟨331283968410028060545403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28269565304322394499874389 331283968410028060545403)
                  ·
                    rfl

theorem cell23_5806559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 8].length) (baseStart_5806559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806559 prefixEnd_5806559 := by exact prefixLift 5806559
  have htrace : WordTrace (prefixWord ++ tailWord_5806559) baseStart_5806559 baseEnd_5806559 := by
    simpa [prefixWord, tailWord_5806559, baseEnd_5806559] using wordTrace_append hprefix tailTrace_5806559
  have hstable : (prefixWord ++ tailWord_5806559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806559).length < 2 ^ (prefixWord ++ tailWord_5806559).sum := by decide
  have hdescent : baseEnd_5806559 < baseStart_5806559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5806563 : List Nat := [1, 1, 1, 6, 3, 1, 2, 1, 3, 4]
def baseStart_5806563 : Nat := 118140960795 + 5806563 * 2 ^ 59
def prefixEnd_5806563 : Nat := 4983230072969 + 3 ^ 40 * 5806563 * 2
def baseEnd_5806563 : Nat := 993852589870956843086203

theorem tailTrace_5806563 : CollatzResearch.WordTrace tailWord_5806563 prefixEnd_5806563 993852589870956843086203 := by
  unfold tailWord_5806563
  simp only [CollatzResearch.WordTrace]
  refine ⟨211782751262821407853672343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141188500841880938569114895 211782751262821407853672343)
  ·
    refine ⟨317674126894232111780508515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211782751262821407853672343 317674126894232111780508515)
    ·
      refine ⟨476511190341348167670762773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317674126894232111780508515 476511190341348167670762773)
      ·
        refine ⟨22336462047250695359567005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 476511190341348167670762773 22336462047250695359567005)
        ·
          refine ⟨8376173267719010759837627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22336462047250695359567005 8376173267719010759837627)
          ·
            refine ⟨12564259901578516139756441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8376173267719010759837627 12564259901578516139756441)
            ·
              refine ⟨9423194926183887104817331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12564259901578516139756441 9423194926183887104817331)
              ·
                refine ⟨14134792389275830657225997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9423194926183887104817331 14134792389275830657225997)
                ·
                  refine ⟨5300547145978436496459749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14134792389275830657225997 5300547145978436496459749)
                  ·
                    refine ⟨993852589870956843086203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5300547145978436496459749 993852589870956843086203)
                    ·
                      rfl

theorem cell23_5806563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 3, 4].length) (baseStart_5806563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806563 prefixEnd_5806563 := by exact prefixLift 5806563
  have htrace : WordTrace (prefixWord ++ tailWord_5806563) baseStart_5806563 baseEnd_5806563 := by
    simpa [prefixWord, tailWord_5806563, baseEnd_5806563] using wordTrace_append hprefix tailTrace_5806563
  have hstable : (prefixWord ++ tailWord_5806563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806563).length < 2 ^ (prefixWord ++ tailWord_5806563).sum := by decide
  have hdescent : baseEnd_5806563 < baseStart_5806563 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5806576 : List Nat := [2, 1, 1, 1, 3, 3, 5, 1, 6]
def baseStart_5806576 : Nat := 118140960795 + 5806576 * 2 ^ 59
def prefixEnd_5806576 : Nat := 4983230072969 + 3 ^ 40 * 5806576 * 2
def baseEnd_5806576 : Nat := 331284938317930997599561

theorem tailTrace_5806576 : CollatzResearch.WordTrace tailWord_5806576 prefixEnd_5806576 331284938317930997599561 := by
  unfold tailWord_5806576
  simp only [CollatzResearch.WordTrace]
  refine ⟨105891612705887155536947791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141188816941182874049263721 105891612705887155536947791)
  ·
    refine ⟨158837419058830733305421687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105891612705887155536947791 158837419058830733305421687)
    ·
      refine ⟨238256128588246099958132531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158837419058830733305421687 238256128588246099958132531)
      ·
        refine ⟨357384192882369149937198797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238256128588246099958132531 357384192882369149937198797)
        ·
          refine ⟨134019072330888431226449549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 357384192882369149937198797 134019072330888431226449549)
          ·
            refine ⟨50257152124083161709918581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134019072330888431226449549 50257152124083161709918581)
            ·
              refine ⟨4711608011632796410304867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50257152124083161709918581 4711608011632796410304867)
              ·
                refine ⟨7067412017449194615457301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4711608011632796410304867 7067412017449194615457301)
                ·
                  refine ⟨331284938317930997599561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7067412017449194615457301 331284938317930997599561)
                  ·
                    rfl

theorem cell23_5806576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 1, 6].length) (baseStart_5806576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806576 prefixEnd_5806576 := by exact prefixLift 5806576
  have htrace : WordTrace (prefixWord ++ tailWord_5806576) baseStart_5806576 baseEnd_5806576 := by
    simpa [prefixWord, tailWord_5806576, baseEnd_5806576] using wordTrace_append hprefix tailTrace_5806576
  have hstable : (prefixWord ++ tailWord_5806576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806576).length < 2 ^ (prefixWord ++ tailWord_5806576).sum := by decide
  have hdescent : baseEnd_5806576 < baseStart_5806576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5806586 : List Nat := [3, 1, 1, 1, 1, 2, 2, 3, 5, 1, 3]
def baseStart_5806586 : Nat := 118140960795 + 5806586 * 2 ^ 59
def prefixEnd_5806586 : Nat := 4983230072969 + 3 ^ 40 * 5806586 * 2
def baseEnd_5806586 : Nat := 2981569579667923939271003

theorem tailTrace_5806586 : CollatzResearch.WordTrace tailWord_5806586 prefixEnd_5806586 2981569579667923939271003 := by
  unfold tailWord_5806586
  simp only [CollatzResearch.WordTrace]
  refine ⟨52945897535434520695439903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141189060094492055187839741 52945897535434520695439903)
  ·
    refine ⟨79418846303151781043159855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52945897535434520695439903 79418846303151781043159855)
    ·
      refine ⟨119128269454727671564739783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79418846303151781043159855 119128269454727671564739783)
      ·
        refine ⟨178692404182091507347109675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119128269454727671564739783 178692404182091507347109675)
        ·
          refine ⟨268038606273137261020664513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178692404182091507347109675 268038606273137261020664513)
          ·
            refine ⟨201028954704852945765498385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268038606273137261020664513 201028954704852945765498385)
            ·
              refine ⟨150771716028639709324123789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201028954704852945765498385 150771716028639709324123789)
              ·
                refine ⟨56539393510739890996546421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150771716028639709324123789 56539393510739890996546421)
                ·
                  refine ⟨5300568141631864780926227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56539393510739890996546421 5300568141631864780926227)
                  ·
                    refine ⟨7950852212447797171389341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5300568141631864780926227 7950852212447797171389341)
                    ·
                      refine ⟨2981569579667923939271003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7950852212447797171389341 2981569579667923939271003)
                      ·
                        rfl

theorem cell23_5806586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 5, 1, 3].length) (baseStart_5806586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806586 prefixEnd_5806586 := by exact prefixLift 5806586
  have htrace : WordTrace (prefixWord ++ tailWord_5806586) baseStart_5806586 baseEnd_5806586 := by
    simpa [prefixWord, tailWord_5806586, baseEnd_5806586] using wordTrace_append hprefix tailTrace_5806586
  have hstable : (prefixWord ++ tailWord_5806586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806586).length < 2 ^ (prefixWord ++ tailWord_5806586).sum := by decide
  have hdescent : baseEnd_5806586 < baseStart_5806586 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5806613 : List Nat := [1, 3, 2, 1, 3, 1, 3, 2, 2, 3, 2]
def baseStart_5806613 : Nat := 118140960795 + 5806613 * 2 ^ 59
def prefixEnd_5806613 : Nat := 4983230072969 + 3 ^ 40 * 5806613 * 2
def baseEnd_5806613 : Nat := 2981583443645595333633379

theorem tailTrace_5806613 : CollatzResearch.WordTrace tailWord_5806613 prefixEnd_5806613 2981583443645595333633379 := by
  unfold tailWord_5806613
  simp only [CollatzResearch.WordTrace]
  refine ⟨211784574912640266392992493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141189716608426844261994995 211784574912640266392992493)
  ·
    refine ⟨79419215592240099897372185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211784574912640266392992493 79419215592240099897372185)
    ·
      refine ⟨59564411694180074923029139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79419215592240099897372185 59564411694180074923029139)
      ·
        refine ⟨89346617541270112384543709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59564411694180074923029139 89346617541270112384543709)
        ·
          refine ⟨33504981577976292144203891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89346617541270112384543709 33504981577976292144203891)
          ·
            refine ⟨50257472366964438216305837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33504981577976292144203891 50257472366964438216305837)
            ·
              refine ⟨18846552137611664331114689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50257472366964438216305837 18846552137611664331114689)
              ·
                refine ⟨14134914103208748248336017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18846552137611664331114689 14134914103208748248336017)
                ·
                  refine ⟨10601185577406561186252013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14134914103208748248336017 10601185577406561186252013)
                  ·
                    refine ⟨3975444591527460444844505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10601185577406561186252013 3975444591527460444844505)
                    ·
                      refine ⟨2981583443645595333633379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3975444591527460444844505 2981583443645595333633379)
                      ·
                        rfl

theorem cell23_5806613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 2, 3, 2].length) (baseStart_5806613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806613 prefixEnd_5806613 := by exact prefixLift 5806613
  have htrace : WordTrace (prefixWord ++ tailWord_5806613) baseStart_5806613 baseEnd_5806613 := by
    simpa [prefixWord, tailWord_5806613, baseEnd_5806613] using wordTrace_append hprefix tailTrace_5806613
  have hstable : (prefixWord ++ tailWord_5806613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806613).length < 2 ^ (prefixWord ++ tailWord_5806613).sum := by decide
  have hdescent : baseEnd_5806613 < baseStart_5806613 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5806620 : List Nat := [2, 2, 3, 1, 2, 4, 1, 1, 3, 1, 3]
def baseStart_5806620 : Nat := 118140960795 + 5806620 * 2 ^ 59
def prefixEnd_5806620 : Nat := 4983230072969 + 3 ^ 40 * 5806620 * 2
def baseEnd_5806620 : Nat := 2981587038010176806245847

theorem tailTrace_5806620 : CollatzResearch.WordTrace tailWord_5806620 prefixEnd_5806620 2981587038010176806245847 := by
  unfold tailWord_5806620
  simp only [CollatzResearch.WordTrace]
  refine ⟨105892415111807453294248657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141189886815743271058998209 105892415111807453294248657)
  ·
    refine ⟨79419311333855589970686493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105892415111807453294248657 79419311333855589970686493)
    ·
      refine ⟨29782241750195846239007435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79419311333855589970686493 29782241750195846239007435)
      ·
        refine ⟨44673362625293769358511153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29782241750195846239007435 44673362625293769358511153)
        ·
          refine ⟨33505021968970327018883365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44673362625293769358511153 33505021968970327018883365)
          ·
            refine ⟨6282191619181936316040631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33505021968970327018883365 6282191619181936316040631)
            ·
              refine ⟨9423287428772904474060947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6282191619181936316040631 9423287428772904474060947)
              ·
                refine ⟨14134931143159356711091421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9423287428772904474060947 14134931143159356711091421)
                ·
                  refine ⟨5300599178684758766659283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14134931143159356711091421 5300599178684758766659283)
                  ·
                    refine ⟨7950898768027138149988925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5300599178684758766659283 7950898768027138149988925)
                    ·
                      refine ⟨2981587038010176806245847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7950898768027138149988925 2981587038010176806245847)
                      ·
                        rfl

theorem cell23_5806620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_5806620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806620 prefixEnd_5806620 := by exact prefixLift 5806620
  have htrace : WordTrace (prefixWord ++ tailWord_5806620) baseStart_5806620 baseEnd_5806620 := by
    simpa [prefixWord, tailWord_5806620, baseEnd_5806620] using wordTrace_append hprefix tailTrace_5806620
  have hstable : (prefixWord ++ tailWord_5806620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806620).length < 2 ^ (prefixWord ++ tailWord_5806620).sum := by decide
  have hdescent : baseEnd_5806620 < baseStart_5806620 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5806626 : List Nat := [3, 3, 1, 1, 1, 1, 1, 4, 3, 1, 4]
def baseStart_5806626 : Nat := 118140960795 + 5806626 * 2 ^ 59
def prefixEnd_5806626 : Nat := 4983230072969 + 3 ^ 40 * 5806626 * 2
def baseEnd_5806626 : Nat := 2981590118894103782770819

theorem tailTrace_5806626 : CollatzResearch.WordTrace tailWord_5806626 prefixEnd_5806626 2981590118894103782770819 := by
  unfold tailWord_5806626
  simp only [CollatzResearch.WordTrace]
  refine ⟨52946262265398292403303933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141190032707728779742143821 52946262265398292403303933)
  ·
    refine ⟨19854848349524359651238975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52946262265398292403303933 19854848349524359651238975)
    ·
      refine ⟨29782272524286539476858463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19854848349524359651238975 29782272524286539476858463)
      ·
        refine ⟨44673408786429809215287695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29782272524286539476858463 44673408786429809215287695)
        ·
          refine ⟨67010113179644713822931543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44673408786429809215287695 67010113179644713822931543)
          ·
            refine ⟨100515169769467070734397315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67010113179644713822931543 100515169769467070734397315)
            ·
              refine ⟨150772754654200606101595973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100515169769467070734397315 150772754654200606101595973)
              ·
                refine ⟨28269891497662613644049245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 150772754654200606101595973 28269891497662613644049245)
                ·
                  refine ⟨10601209311623480116518467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28269891497662613644049245 10601209311623480116518467)
                  ·
                    refine ⟨15901813967435220174777701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10601209311623480116518467 15901813967435220174777701)
                    ·
                      refine ⟨2981590118894103782770819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15901813967435220174777701 2981590118894103782770819)
                      ·
                        rfl

theorem cell23_5806626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_5806626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806626 prefixEnd_5806626 := by exact prefixLift 5806626
  have htrace : WordTrace (prefixWord ++ tailWord_5806626) baseStart_5806626 baseEnd_5806626 := by
    simpa [prefixWord, tailWord_5806626, baseEnd_5806626] using wordTrace_append hprefix tailTrace_5806626
  have hstable : (prefixWord ++ tailWord_5806626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806626).length < 2 ^ (prefixWord ++ tailWord_5806626).sum := by decide
  have hdescent : baseEnd_5806626 < baseStart_5806626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5806639 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 7, 2, 4]
def baseStart_5806639 : Nat := 118140960795 + 5806639 * 2 ^ 59
def prefixEnd_5806639 : Nat := 4983230072969 + 3 ^ 40 * 5806639 * 2
def baseEnd_5806639 : Nat := 2981596794142612231908259

theorem tailTrace_5806639 : CollatzResearch.WordTrace tailWord_5806639 prefixEnd_5806639 2981596794142612231908259 := by
  unfold tailWord_5806639
  simp only [CollatzResearch.WordTrace]
  refine ⟨211785523210546072833438971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141190348807030715222292647 211785523210546072833438971)
  ·
    refine ⟨317678284815819109250158457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211785523210546072833438971 317678284815819109250158457)
    ·
      refine ⟨238258713611864331937618843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317678284815819109250158457 238258713611864331937618843)
      ·
        refine ⟨357388070417796497906428265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238258713611864331937618843 357388070417796497906428265)
        ·
          refine ⟨268041052813347373429821199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 357388070417796497906428265 268041052813347373429821199)
          ·
            refine ⟨402061579220021060144731799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268041052813347373429821199 402061579220021060144731799)
            ·
              refine ⟨603092368830031590217097699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 402061579220021060144731799 603092368830031590217097699)
              ·
                refine ⟨904638553245047385325646549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 603092368830031590217097699 904638553245047385325646549)
                ·
                  refine ⟨21202466091680798093569841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 904638553245047385325646549 21202466091680798093569841)
                  ·
                    refine ⟨15901849568760598570177381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21202466091680798093569841 15901849568760598570177381)
                    ·
                      refine ⟨2981596794142612231908259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15901849568760598570177381 2981596794142612231908259)
                      ·
                        rfl

theorem cell23_5806639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 2, 4].length) (baseStart_5806639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806639 prefixEnd_5806639 := by exact prefixLift 5806639
  have htrace : WordTrace (prefixWord ++ tailWord_5806639) baseStart_5806639 baseEnd_5806639 := by
    simpa [prefixWord, tailWord_5806639, baseEnd_5806639] using wordTrace_append hprefix tailTrace_5806639
  have hstable : (prefixWord ++ tailWord_5806639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806639).length < 2 ^ (prefixWord ++ tailWord_5806639).sum := by decide
  have hdescent : baseEnd_5806639 < baseStart_5806639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5806643 : List Nat := [1, 1, 1, 2, 4, 2, 2, 1, 5, 2, 2]
def baseStart_5806643 : Nat := 118140960795 + 5806643 * 2 ^ 59
def prefixEnd_5806643 : Nat := 4983230072969 + 3 ^ 40 * 5806643 * 2
def baseEnd_5806643 : Nat := 2981598848065230216258241

theorem tailTrace_5806643 : CollatzResearch.WordTrace tailWord_5806643 prefixEnd_5806643 2981598848065230216258241 := by
  unfold tailWord_5806643
  simp only [CollatzResearch.WordTrace]
  refine ⟨211785669102531581516584583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141190446068354387677723055 211785669102531581516584583)
  ·
    refine ⟨317678503653797372274876875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211785669102531581516584583 317678503653797372274876875)
    ·
      refine ⟨476517755480696058412315313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317678503653797372274876875 476517755480696058412315313)
      ·
        refine ⟨357388316610522043809236485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 476517755480696058412315313 357388316610522043809236485)
        ·
          refine ⟨67010309364472883214231841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 357388316610522043809236485 67010309364472883214231841)
          ·
            refine ⟨50257732023354662410673881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67010309364472883214231841 50257732023354662410673881)
            ·
              refine ⟨37693299017515996808005411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50257732023354662410673881 37693299017515996808005411)
              ·
                refine ⟨56539948526273995212008117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37693299017515996808005411 56539948526273995212008117)
                ·
                  refine ⟨5300620174338187051125761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56539948526273995212008117 5300620174338187051125761)
                  ·
                    refine ⟨3975465130753640288344321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5300620174338187051125761 3975465130753640288344321)
                    ·
                      refine ⟨2981598848065230216258241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3975465130753640288344321 2981598848065230216258241)
                      ·
                        rfl

theorem cell23_5806643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 5, 2, 2].length) (baseStart_5806643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806643 prefixEnd_5806643 := by exact prefixLift 5806643
  have htrace : WordTrace (prefixWord ++ tailWord_5806643) baseStart_5806643 baseEnd_5806643 := by
    simpa [prefixWord, tailWord_5806643, baseEnd_5806643] using wordTrace_append hprefix tailTrace_5806643
  have hstable : (prefixWord ++ tailWord_5806643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806643).length < 2 ^ (prefixWord ++ tailWord_5806643).sum := by decide
  have hdescent : baseEnd_5806643 < baseStart_5806643 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5806649 : List Nat := [1, 2, 1, 5, 1, 1, 1, 11]
def baseStart_5806649 : Nat := 118140960795 + 5806649 * 2 ^ 59
def prefixEnd_5806649 : Nat := 4983230072969 + 3 ^ 40 * 5806649 * 2
def baseEnd_5806649 : Nat := 110429701072191007140119

theorem tailTrace_5806649 : CollatzResearch.WordTrace tailWord_5806649 prefixEnd_5806649 110429701072191007140119 := by
  unfold tailWord_5806649
  simp only [CollatzResearch.WordTrace]
  refine ⟨211785887940509844541303001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141190591960339896360868667 211785887940509844541303001)
  ·
    refine ⟨158839415955382383405977251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211785887940509844541303001 158839415955382383405977251)
    ·
      refine ⟨238259123933073575108965877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158839415955382383405977251 238259123933073575108965877)
      ·
        refine ⟨22336792868725647666465551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 238259123933073575108965877 22336792868725647666465551)
        ·
          refine ⟨33505189303088471499698327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22336792868725647666465551 33505189303088471499698327)
          ·
            refine ⟨50257783954632707249547491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33505189303088471499698327 50257783954632707249547491)
            ·
              refine ⟨75386675931949060874321237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50257783954632707249547491 75386675931949060874321237)
              ·
                refine ⟨110429701072191007140119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 75386675931949060874321237 110429701072191007140119)
                ·
                  rfl

theorem cell23_5806649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 11].length) (baseStart_5806649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806649 prefixEnd_5806649 := by exact prefixLift 5806649
  have htrace : WordTrace (prefixWord ++ tailWord_5806649) baseStart_5806649 baseEnd_5806649 := by
    simpa [prefixWord, tailWord_5806649, baseEnd_5806649] using wordTrace_append hprefix tailTrace_5806649
  have hstable : (prefixWord ++ tailWord_5806649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806649).length < 2 ^ (prefixWord ++ tailWord_5806649).sum := by decide
  have hdescent : baseEnd_5806649 < baseStart_5806649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5806663 : List Nat := [1, 1, 4, 1, 4, 3, 1, 1, 1, 1, 5]
def baseStart_5806663 : Nat := 118140960795 + 5806663 * 2 ^ 59
def prefixEnd_5806663 : Nat := 4983230072969 + 3 ^ 40 * 5806663 * 2
def baseEnd_5806663 : Nat := 2981609117678320138008149

theorem tailTrace_5806663 : CollatzResearch.WordTrace tailWord_5806663 prefixEnd_5806663 2981609117678320138008149 := by
  unfold tailWord_5806663
  simp only [CollatzResearch.WordTrace]
  refine ⟨211786398562459124932312643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141190932374972749954875095 211786398562459124932312643)
  ·
    refine ⟨317679597843688687398468965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211786398562459124932312643 317679597843688687398468965)
    ·
      refine ⟨59564924595691628887212931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 317679597843688687398468965 59564924595691628887212931)
      ·
        refine ⟨89347386893537443330819397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59564924595691628887212931 89347386893537443330819397)
        ·
          refine ⟨16752635042538270624528637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89347386893537443330819397 16752635042538270624528637)
          ·
            refine ⟨6282238140951851484198239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16752635042538270624528637 6282238140951851484198239)
            ·
              refine ⟨9423357211427777226297359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6282238140951851484198239 9423357211427777226297359)
              ·
                refine ⟨14135035817141665839446039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9423357211427777226297359 14135035817141665839446039)
                ·
                  refine ⟨21202553725712498759169059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14135035817141665839446039 21202553725712498759169059)
                  ·
                    refine ⟨31803830588568748138753589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21202553725712498759169059 31803830588568748138753589)
                    ·
                      refine ⟨2981609117678320138008149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31803830588568748138753589 2981609117678320138008149)
                      ·
                        rfl

theorem cell23_5806663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 1, 5].length) (baseStart_5806663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806663 prefixEnd_5806663 := by exact prefixLift 5806663
  have htrace : WordTrace (prefixWord ++ tailWord_5806663) baseStart_5806663 baseEnd_5806663 := by
    simpa [prefixWord, tailWord_5806663, baseEnd_5806663] using wordTrace_append hprefix tailTrace_5806663
  have hstable : (prefixWord ++ tailWord_5806663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806663).length < 2 ^ (prefixWord ++ tailWord_5806663).sum := by decide
  have hdescent : baseEnd_5806663 < baseStart_5806663 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5806679 : List Nat := [1, 1, 3, 2, 2, 2, 1, 1, 1, 9]
def baseStart_5806679 : Nat := 118140960795 + 5806679 * 2 ^ 59
def prefixEnd_5806679 : Nat := 4983230072969 + 3 ^ 40 * 5806679 * 2
def baseEnd_5806679 : Nat := 993872444456264025136025

theorem tailTrace_5806679 : CollatzResearch.WordTrace tailWord_5806679 prefixEnd_5806679 993872444456264025136025 := by
  unfold tailWord_5806679
  simp only [CollatzResearch.WordTrace]
  refine ⟨211786982130401159664895091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141191321420267439776596727 211786982130401159664895091)
  ·
    refine ⟨317680473195601739497342637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211786982130401159664895091 317680473195601739497342637)
    ·
      refine ⟨119130177448350652311503489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 317680473195601739497342637 119130177448350652311503489)
      ·
        refine ⟨89347633086262989233627617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119130177448350652311503489 89347633086262989233627617)
        ·
          refine ⟨67010724814697241925220713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89347633086262989233627617 67010724814697241925220713)
          ·
            refine ⟨50258043611022931443915535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67010724814697241925220713 50258043611022931443915535)
            ·
              refine ⟨75387065416534397165873303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50258043611022931443915535 75387065416534397165873303)
              ·
                refine ⟨113080598124801595748809955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75387065416534397165873303 113080598124801595748809955)
                ·
                  refine ⟨169620897187202393623214933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113080598124801595748809955 169620897187202393623214933)
                  ·
                    refine ⟨993872444456264025136025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 169620897187202393623214933 993872444456264025136025)
                    ·
                      rfl

theorem cell23_5806679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 9].length) (baseStart_5806679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806679 prefixEnd_5806679 := by exact prefixLift 5806679
  have htrace : WordTrace (prefixWord ++ tailWord_5806679) baseStart_5806679 baseEnd_5806679 := by
    simpa [prefixWord, tailWord_5806679, baseEnd_5806679] using wordTrace_append hprefix tailTrace_5806679
  have hstable : (prefixWord ++ tailWord_5806679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806679).length < 2 ^ (prefixWord ++ tailWord_5806679).sum := by decide
  have hdescent : baseEnd_5806679 < baseStart_5806679 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5806703 : List Nat := [1, 1, 2, 1, 3, 2, 4, 1, 3, 3, 2]
def baseStart_5806703 : Nat := 118140960795 + 5806703 * 2 ^ 59
def prefixEnd_5806703 : Nat := 4983230072969 + 3 ^ 40 * 5806703 * 2
def baseEnd_5806703 : Nat := 2981629656904499981507965

theorem tailTrace_5806703 : CollatzResearch.WordTrace tailWord_5806703 prefixEnd_5806703 2981629656904499981507965 := by
  unfold tailWord_5806703
  simp only [CollatzResearch.WordTrace]
  refine ⟨211787857482314211763768763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141191904988209474509179175 211787857482314211763768763)
  ·
    refine ⟨317681786223471317645653145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211787857482314211763768763 317681786223471317645653145)
    ·
      refine ⟨238261339667603488234239859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317681786223471317645653145 238261339667603488234239859)
      ·
        refine ⟨357392009501405232351359789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238261339667603488234239859 357392009501405232351359789)
        ·
          refine ⟨134022003563026962131759921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 357392009501405232351359789 134022003563026962131759921)
          ·
            refine ⟨100516502672270221598819941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134022003563026962131759921 100516502672270221598819941)
            ·
              refine ⟨18846844251050666549778739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100516502672270221598819941 18846844251050666549778739)
              ·
                refine ⟨28270266376575999824668109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18846844251050666549778739 28270266376575999824668109)
                ·
                  refine ⟨10601349891215999934250541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28270266376575999824668109 10601349891215999934250541)
                  ·
                    refine ⟨3975506209205999975343953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10601349891215999934250541 3975506209205999975343953)
                    ·
                      refine ⟨2981629656904499981507965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3975506209205999975343953 2981629656904499981507965)
                      ·
                        rfl

theorem cell23_5806703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 3, 3, 2].length) (baseStart_5806703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806703 prefixEnd_5806703 := by exact prefixLift 5806703
  have htrace : WordTrace (prefixWord ++ tailWord_5806703) baseStart_5806703 baseEnd_5806703 := by
    simpa [prefixWord, tailWord_5806703, baseEnd_5806703] using wordTrace_append hprefix tailTrace_5806703
  have hstable : (prefixWord ++ tailWord_5806703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806703).length < 2 ^ (prefixWord ++ tailWord_5806703).sum := by decide
  have hdescent : baseEnd_5806703 < baseStart_5806703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5806720 : List Nat := [2, 1, 1, 2, 1, 6, 1, 3, 1, 3, 2]
def baseStart_5806720 : Nat := 118140960795 + 5806720 * 2 ^ 59
def prefixEnd_5806720 : Nat := 4983230072969 + 3 ^ 40 * 5806720 * 2
def baseEnd_5806720 : Nat := 2981638386075626414995387

theorem tailTrace_5806720 : CollatzResearch.WordTrace tailWord_5806720 prefixEnd_5806720 2981638386075626414995387 := by
  unfold tailWord_5806720
  simp only [CollatzResearch.WordTrace]
  refine ⟨105894238761626311833568807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141192318348835082444758409 105894238761626311833568807)
  ·
    refine ⟨158841358142439467750353211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105894238761626311833568807 158841358142439467750353211)
    ·
      refine ⟨238262037213659201625529817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158841358142439467750353211 238262037213659201625529817)
      ·
        refine ⟨178696527910244401219147363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238262037213659201625529817 178696527910244401219147363)
        ·
          refine ⟨268044791865366601828721045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178696527910244401219147363 268044791865366601828721045)
          ·
            refine ⟨12564599618689059460721299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 268044791865366601828721045 12564599618689059460721299)
            ·
              refine ⟨18846899428033589191081949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12564599618689059460721299 18846899428033589191081949)
              ·
                refine ⟨7067587285512595946655731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18846899428033589191081949 7067587285512595946655731)
                ·
                  refine ⟨10601380928268893919983597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7067587285512595946655731 10601380928268893919983597)
                  ·
                    refine ⟨3975517848100835219993849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10601380928268893919983597 3975517848100835219993849)
                    ·
                      refine ⟨2981638386075626414995387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3975517848100835219993849 2981638386075626414995387)
                      ·
                        rfl

theorem cell23_5806720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 3, 1, 3, 2].length) (baseStart_5806720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806720 prefixEnd_5806720 := by exact prefixLift 5806720
  have htrace : WordTrace (prefixWord ++ tailWord_5806720) baseStart_5806720 baseEnd_5806720 := by
    simpa [prefixWord, tailWord_5806720, baseEnd_5806720] using wordTrace_append hprefix tailTrace_5806720
  have hstable : (prefixWord ++ tailWord_5806720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806720).length < 2 ^ (prefixWord ++ tailWord_5806720).sum := by decide
  have hdescent : baseEnd_5806720 < baseStart_5806720 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5806739 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 11]
def baseStart_5806739 : Nat := 118140960795 + 5806739 * 2 ^ 59
def prefixEnd_5806739 : Nat := 4983230072969 + 3 ^ 40 * 5806739 * 2
def baseEnd_5806739 : Nat := 331294238023117982295311

theorem tailTrace_5806739 : CollatzResearch.WordTrace tailWord_5806739 prefixEnd_5806739 331294238023117982295311 := by
  unfold tailWord_5806739
  simp only [CollatzResearch.WordTrace]
  refine ⟨211789170510183789912079271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141192780340122526608052847 211789170510183789912079271)
  ·
    refine ⟨317683755765275684868118907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211789170510183789912079271 317683755765275684868118907)
    ·
      refine ⟨476525633647913527302178361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317683755765275684868118907 476525633647913527302178361)
      ·
        refine ⟨357394225235935145476633771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 476525633647913527302178361 357394225235935145476633771)
        ·
          refine ⟨536091337853902718214950657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357394225235935145476633771 536091337853902718214950657)
          ·
            refine ⟨402068503390427038661212993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 536091337853902718214950657 402068503390427038661212993)
            ·
              refine ⟨301551377542820278995909745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 402068503390427038661212993 301551377542820278995909745)
              ·
                refine ⟨226163533157115209246932309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 301551377542820278995909745 226163533157115209246932309)
                ·
                  refine ⟨331294238023117982295311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 226163533157115209246932309 331294238023117982295311)
                  ·
                    rfl

theorem cell23_5806739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 11].length) (baseStart_5806739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806739 prefixEnd_5806739 := by exact prefixLift 5806739
  have htrace : WordTrace (prefixWord ++ tailWord_5806739) baseStart_5806739 baseEnd_5806739 := by
    simpa [prefixWord, tailWord_5806739, baseEnd_5806739] using wordTrace_append hprefix tailTrace_5806739
  have hstable : (prefixWord ++ tailWord_5806739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806739).length < 2 ^ (prefixWord ++ tailWord_5806739).sum := by decide
  have hdescent : baseEnd_5806739 < baseStart_5806739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5806756 : List Nat := [2, 3, 1, 2, 2, 1, 1, 4, 7]
def baseStart_5806756 : Nat := 118140960795 + 5806756 * 2 ^ 59
def prefixEnd_5806756 : Nat := 4983230072969 + 3 ^ 40 * 5806756 * 2
def baseEnd_5806756 : Nat := 331295207931020919349469

theorem tailTrace_5806756 : CollatzResearch.WordTrace tailWord_5806756 prefixEnd_5806756 331295207931020919349469 := by
  unfold tailWord_5806756
  simp only [CollatzResearch.WordTrace]
  refine ⟨105894895275561100907724061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141193193700748134543632081 105894895275561100907724061)
  ·
    refine ⟨39710585728335412840396523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105894895275561100907724061 39710585728335412840396523)
    ·
      refine ⟨59565878592503119260594785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39710585728335412840396523 59565878592503119260594785)
      ·
        refine ⟨44674408944377339445446089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59565878592503119260594785 44674408944377339445446089)
        ·
          refine ⟨33505806708283004584084567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44674408944377339445446089 33505806708283004584084567)
          ·
            refine ⟨50258710062424506876126851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33505806708283004584084567 50258710062424506876126851)
            ·
              refine ⟨75388065093636760314190277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50258710062424506876126851 75388065093636760314190277)
              ·
                refine ⟨14135262205056892558910677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75388065093636760314190277 14135262205056892558910677)
                ·
                  refine ⟨331295207931020919349469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14135262205056892558910677 331295207931020919349469)
                  ·
                    rfl

theorem cell23_5806756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 7].length) (baseStart_5806756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806756 prefixEnd_5806756 := by exact prefixLift 5806756
  have htrace : WordTrace (prefixWord ++ tailWord_5806756) baseStart_5806756 baseEnd_5806756 := by
    simpa [prefixWord, tailWord_5806756, baseEnd_5806756] using wordTrace_append hprefix tailTrace_5806756
  have hstable : (prefixWord ++ tailWord_5806756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806756).length < 2 ^ (prefixWord ++ tailWord_5806756).sum := by decide
  have hdescent : baseEnd_5806756 < baseStart_5806756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5806877 : List Nat := [1, 4, 2, 4, 1, 1, 1, 1, 1, 4, 3]
def baseStart_5806877 : Nat := 118140960795 + 5806877 * 2 ^ 59
def prefixEnd_5806877 : Nat := 4983230072969 + 3 ^ 40 * 5806877 * 2
def baseEnd_5806877 : Nat := 2981719002538382300732165

theorem tailTrace_5806877 : CollatzResearch.WordTrace tailWord_5806877 prefixEnd_5806877 2981719002538382300732165 := by
  unfold tailWord_5806877
  simp only [CollatzResearch.WordTrace]
  refine ⟨211794203783683839480602885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141196135855789226320401923 211794203783683839480602885)
  ·
    refine ⟨39711413209440719902613041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 211794203783683839480602885 39711413209440719902613041)
    ·
      refine ⟨29783559907080539926959781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39711413209440719902613041 29783559907080539926959781)
      ·
        refine ⟨5584417482577601236304959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29783559907080539926959781 5584417482577601236304959)
        ·
          refine ⟨8376626223866401854457439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5584417482577601236304959 8376626223866401854457439)
          ·
            refine ⟨12564939335799602781686159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8376626223866401854457439 12564939335799602781686159)
            ·
              refine ⟨18847409003699404172529239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12564939335799602781686159 18847409003699404172529239)
              ·
                refine ⟨28271113505549106258793859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18847409003699404172529239 28271113505549106258793859)
                ·
                  refine ⟨42406670258323659388190789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28271113505549106258793859 42406670258323659388190789)
                  ·
                    refine ⟨7951250673435686135285773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42406670258323659388190789 7951250673435686135285773)
                    ·
                      refine ⟨2981719002538382300732165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7951250673435686135285773 2981719002538382300732165)
                      ·
                        rfl

theorem cell23_5806877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_5806877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806877 prefixEnd_5806877 := by exact prefixLift 5806877
  have htrace : WordTrace (prefixWord ++ tailWord_5806877) baseStart_5806877 baseEnd_5806877 := by
    simpa [prefixWord, tailWord_5806877, baseEnd_5806877] using wordTrace_append hprefix tailTrace_5806877
  have hstable : (prefixWord ++ tailWord_5806877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806877).length < 2 ^ (prefixWord ++ tailWord_5806877).sum := by decide
  have hdescent : baseEnd_5806877 < baseStart_5806877 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
