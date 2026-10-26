import V185TrunkScan23Chunk0582

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3447850 : List Nat := [3, 1, 4, 1, 3, 1, 1, 3, 2, 2, 2]
def baseStart_3447850 : Nat := 118140960795 + 3447850 * 2 ^ 59
def prefixEnd_3447850 : Nat := 4983230072969 + 3 ^ 40 * 3447850 * 2
def baseEnd_3447850 : Nat := 1770404274604440504718633

theorem tailTrace_3447850 : CollatzResearch.WordTrace tailWord_3447850 prefixEnd_3447850 1770404274604440504718633 := by
  unfold tailWord_3447850
  simp only [CollatzResearch.WordTrace]
  refine ⟨31438355139758942686173251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83835613706023847163128669 31438355139758942686173251)
  ·
    refine ⟨47157532709638414029259877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31438355139758942686173251 47157532709638414029259877)
    ·
      refine ⟨8842037383057202630486227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47157532709638414029259877 8842037383057202630486227)
      ·
        refine ⟨13263056074585803945729341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8842037383057202630486227 13263056074585803945729341)
        ·
          refine ⟨4973646027969676479648503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13263056074585803945729341 4973646027969676479648503)
          ·
            refine ⟨7460469041954514719472755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4973646027969676479648503 7460469041954514719472755)
            ·
              refine ⟨11190703562931772079209133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7460469041954514719472755 11190703562931772079209133)
              ·
                refine ⟨4196513836099414529703425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11190703562931772079209133 4196513836099414529703425)
                ·
                  refine ⟨3147385377074560897277569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4196513836099414529703425 3147385377074560897277569)
                  ·
                    refine ⟨2360539032805920672958177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3147385377074560897277569 2360539032805920672958177)
                    ·
                      refine ⟨1770404274604440504718633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2360539032805920672958177 1770404274604440504718633)
                      ·
                        rfl

theorem cell23_3447850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_3447850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3447850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3447850 prefixEnd_3447850 := by exact prefixLift 3447850
  have htrace : WordTrace (prefixWord ++ tailWord_3447850) baseStart_3447850 baseEnd_3447850 := by
    simpa [prefixWord, tailWord_3447850, baseEnd_3447850] using wordTrace_append hprefix tailTrace_3447850
  have hstable : (prefixWord ++ tailWord_3447850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447850).length < 2 ^ (prefixWord ++ tailWord_3447850).sum := by decide
  have hdescent : baseEnd_3447850 < baseStart_3447850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447852 : List Nat := [2, 2, 1, 1, 1, 2, 3, 2, 4, 5]
def baseStart_3447852 : Nat := 118140960795 + 3447852 * 2 ^ 59
def prefixEnd_3447852 : Nat := 4983230072969 + 3 ^ 40 * 3447852 * 2
def baseEnd_3447852 : Nat := 590135100521916498964541

theorem tailTrace_3447852 : CollatzResearch.WordTrace tailWord_3447852 prefixEnd_3447852 590135100521916498964541 := by
  unfold tailWord_3447852
  simp only [CollatzResearch.WordTrace]
  refine ⟨62876746752514262543132905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83835662336685683390843873 62876746752514262543132905)
  ·
    refine ⟨47157560064385696907349679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62876746752514262543132905 47157560064385696907349679)
    ·
      refine ⟨70736340096578545361024519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47157560064385696907349679 70736340096578545361024519)
      ·
        refine ⟨106104510144867818041536779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70736340096578545361024519 106104510144867818041536779)
        ·
          refine ⟨159156765217301727062305169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106104510144867818041536779 159156765217301727062305169)
          ·
            refine ⟨119367573912976295296728877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159156765217301727062305169 119367573912976295296728877)
            ·
              refine ⟨44762840217366110736273329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119367573912976295296728877 44762840217366110736273329)
              ·
                refine ⟨33572130163024583052204997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44762840217366110736273329 33572130163024583052204997)
                ·
                  refine ⟨6294774405567109322288437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33572130163024583052204997 6294774405567109322288437)
                  ·
                    refine ⟨590135100521916498964541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6294774405567109322288437 590135100521916498964541)
                    ·
                      rfl

theorem cell23_3447852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 5].length) (baseStart_3447852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3447852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3447852 prefixEnd_3447852 := by exact prefixLift 3447852
  have htrace : WordTrace (prefixWord ++ tailWord_3447852) baseStart_3447852 baseEnd_3447852 := by
    simpa [prefixWord, tailWord_3447852, baseEnd_3447852] using wordTrace_append hprefix tailTrace_3447852
  have hstable : (prefixWord ++ tailWord_3447852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447852).length < 2 ^ (prefixWord ++ tailWord_3447852).sum := by decide
  have hdescent : baseEnd_3447852 < baseStart_3447852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447869 : List Nat := [1, 4, 1, 3, 1, 2, 1, 3, 2, 5]
def baseStart_3447869 : Nat := 118140960795 + 3447869 * 2 ^ 59
def prefixEnd_3447869 : Nat := 4983230072969 + 3 ^ 40 * 3447869 * 2
def baseEnd_3447869 : Nat := 590138010245625310127015

theorem tailTrace_3447869 : CollatzResearch.WordTrace tailWord_3447869 prefixEnd_3447869 590138010245625310127015 := by
  unfold tailWord_3447869
  simp only [CollatzResearch.WordTrace]
  refine ⟨125754113545966936989634661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83836075697311291326423107 125754113545966936989634661)
  ·
    refine ⟨23578896289868800685556499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125754113545966936989634661 23578896289868800685556499)
    ·
      refine ⟨35368344434803201028334749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23578896289868800685556499 35368344434803201028334749)
      ·
        refine ⟨13263129163051200385625531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35368344434803201028334749 13263129163051200385625531)
        ·
          refine ⟨19894693744576800578438297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13263129163051200385625531 19894693744576800578438297)
          ·
            refine ⟨14921020308432600433828723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19894693744576800578438297 14921020308432600433828723)
            ·
              refine ⟨22381530462648900650743085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14921020308432600433828723 22381530462648900650743085)
              ·
                refine ⟨8393073923493337744028657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22381530462648900650743085 8393073923493337744028657)
                ·
                  refine ⟨6294805442620003308021493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8393073923493337744028657 6294805442620003308021493)
                  ·
                    refine ⟨590138010245625310127015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6294805442620003308021493 590138010245625310127015)
                    ·
                      rfl

theorem cell23_3447869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 2, 5].length) (baseStart_3447869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3447869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3447869 prefixEnd_3447869 := by exact prefixLift 3447869
  have htrace : WordTrace (prefixWord ++ tailWord_3447869) baseStart_3447869 baseEnd_3447869 := by
    simpa [prefixWord, tailWord_3447869, baseEnd_3447869] using wordTrace_append hprefix tailTrace_3447869
  have hstable : (prefixWord ++ tailWord_3447869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447869).length < 2 ^ (prefixWord ++ tailWord_3447869).sum := by decide
  have hdescent : baseEnd_3447869 < baseStart_3447869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447889 : List Nat := [1, 2, 2, 1, 3, 1, 4, 2, 2, 1, 4]
def baseStart_3447889 : Nat := 118140960795 + 3447889 * 2 ^ 59
def prefixEnd_3447889 : Nat := 4983230072969 + 3 ^ 40 * 3447889 * 2
def baseEnd_3447889 : Nat := 1770424300349965852130953

theorem tailTrace_3447889 : CollatzResearch.WordTrace tailWord_3447889 prefixEnd_3447889 1770424300349965852130953 := by
  unfold tailWord_3447889
  simp only [CollatzResearch.WordTrace]
  refine ⟨125754843005894480405362721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83836562003929653603575147 125754843005894480405362721)
  ·
    refine ⟨94316132254420860304022041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125754843005894480405362721 94316132254420860304022041)
    ·
      refine ⟨70737099190815645228016531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94316132254420860304022041 70737099190815645228016531)
      ·
        refine ⟨106105648786223467842024797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70737099190815645228016531 106105648786223467842024797)
        ·
          refine ⟨39789618294833800440759299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106105648786223467842024797 39789618294833800440759299)
          ·
            refine ⟨59684427442250700661138949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39789618294833800440759299 59684427442250700661138949)
            ·
              refine ⟨11190830145422006373963553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59684427442250700661138949 11190830145422006373963553)
              ·
                refine ⟨8393122609066504780472665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11190830145422006373963553 8393122609066504780472665)
                ·
                  refine ⟨6294841956799878585354499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8393122609066504780472665 6294841956799878585354499)
                  ·
                    refine ⟨9442262935199817878031749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6294841956799878585354499 9442262935199817878031749)
                    ·
                      refine ⟨1770424300349965852130953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9442262935199817878031749 1770424300349965852130953)
                      ·
                        rfl

theorem cell23_3447889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 2, 1, 4].length) (baseStart_3447889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3447889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3447889 prefixEnd_3447889 := by exact prefixLift 3447889
  have htrace : WordTrace (prefixWord ++ tailWord_3447889) baseStart_3447889 baseEnd_3447889 := by
    simpa [prefixWord, tailWord_3447889, baseEnd_3447889] using wordTrace_append hprefix tailTrace_3447889
  have hstable : (prefixWord ++ tailWord_3447889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447889).length < 2 ^ (prefixWord ++ tailWord_3447889).sum := by decide
  have hdescent : baseEnd_3447889 < baseStart_3447889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447909 : List Nat := [1, 3, 1, 3, 2, 1, 2, 2, 1, 4, 3]
def baseStart_3447909 : Nat := 118140960795 + 3447909 * 2 ^ 59
def prefixEnd_3447909 : Nat := 4983230072969 + 3 ^ 40 * 3447909 * 2
def baseEnd_3447909 : Nat := 1770434569963055773880861

theorem tailTrace_3447909 : CollatzResearch.WordTrace tailWord_3447909 prefixEnd_3447909 1770434569963055773880861 := by
  unfold tailWord_3447909
  simp only [CollatzResearch.WordTrace]
  refine ⟨125755572465822023821090781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83837048310548015880727187 125755572465822023821090781)
  ·
    refine ⟨47158339674683258932909043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125755572465822023821090781 47158339674683258932909043)
    ·
      refine ⟨70737509512024888399363565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47158339674683258932909043 70737509512024888399363565)
      ·
        refine ⟨26526566067009333149761337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70737509512024888399363565 26526566067009333149761337)
        ·
          refine ⟨19894924550256999862321003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26526566067009333149761337 19894924550256999862321003)
          ·
            refine ⟨29842386825385499793481505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19894924550256999862321003 29842386825385499793481505)
            ·
              refine ⟨22381790119039124845111129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29842386825385499793481505 22381790119039124845111129)
              ·
                refine ⟨16786342589279343633833347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22381790119039124845111129 16786342589279343633833347)
                ·
                  refine ⟨25179513883919015450750021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16786342589279343633833347 25179513883919015450750021)
                  ·
                    refine ⟨4721158853234815397015629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25179513883919015450750021 4721158853234815397015629)
                    ·
                      refine ⟨1770434569963055773880861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4721158853234815397015629 1770434569963055773880861)
                      ·
                        rfl

theorem cell23_3447909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_3447909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3447909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3447909 prefixEnd_3447909 := by exact prefixLift 3447909
  have htrace : WordTrace (prefixWord ++ tailWord_3447909) baseStart_3447909 baseEnd_3447909 := by
    simpa [prefixWord, tailWord_3447909, baseEnd_3447909] using wordTrace_append hprefix tailTrace_3447909
  have hstable : (prefixWord ++ tailWord_3447909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447909).length < 2 ^ (prefixWord ++ tailWord_3447909).sum := by decide
  have hdescent : baseEnd_3447909 < baseStart_3447909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447926 : List Nat := [5, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3]
def baseStart_3447926 : Nat := 118140960795 + 3447926 * 2 ^ 59
def prefixEnd_3447926 : Nat := 4983230072969 + 3 ^ 40 * 3447926 * 2
def baseEnd_3447926 : Nat := 1770443299134182207368283

theorem tailTrace_3447926 : CollatzResearch.WordTrace tailWord_3447926 prefixEnd_3447926 1770443299134182207368283 := by
  unfold tailWord_3447926
  simp only [CollatzResearch.WordTrace]
  refine ⟨7859762031672527232778727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83837461671173623816306421 7859762031672527232778727)
  ·
    refine ⟨11789643047508790849168091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7859762031672527232778727 11789643047508790849168091)
    ·
      refine ⟨17684464571263186273752137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11789643047508790849168091 17684464571263186273752137)
      ·
        refine ⟨13263348428447389705314103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17684464571263186273752137 13263348428447389705314103)
        ·
          refine ⟨19895022642671084557971155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13263348428447389705314103 19895022642671084557971155)
          ·
            refine ⟨29842533964006626836956733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19895022642671084557971155 29842533964006626836956733)
            ·
              refine ⟨11190950236502485063858775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29842533964006626836956733 11190950236502485063858775)
              ·
                refine ⟨16786425354753727595788163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11190950236502485063858775 16786425354753727595788163)
                ·
                  refine ⟨25179638032130591393682245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16786425354753727595788163 25179638032130591393682245)
                  ·
                    refine ⟨4721182131024485886315421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25179638032130591393682245 4721182131024485886315421)
                    ·
                      refine ⟨1770443299134182207368283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4721182131024485886315421 1770443299134182207368283)
                      ·
                        rfl

theorem cell23_3447926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_3447926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3447926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3447926 prefixEnd_3447926 := by exact prefixLift 3447926
  have htrace : WordTrace (prefixWord ++ tailWord_3447926) baseStart_3447926 baseEnd_3447926 := by
    simpa [prefixWord, tailWord_3447926, baseEnd_3447926] using wordTrace_append hprefix tailTrace_3447926
  have hstable : (prefixWord ++ tailWord_3447926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447926).length < 2 ^ (prefixWord ++ tailWord_3447926).sum := by decide
  have hdescent : baseEnd_3447926 < baseStart_3447926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447933 : List Nat := [1, 4, 1, 1, 3, 1, 4, 3, 1, 4]
def baseStart_3447933 : Nat := 118140960795 + 3447933 * 2 ^ 59
def prefixEnd_3447933 : Nat := 4983230072969 + 3 ^ 40 * 3447933 * 2
def baseEnd_3447933 : Nat := 590148964499587893326917

theorem tailTrace_3447933 : CollatzResearch.WordTrace tailWord_3447933 prefixEnd_3447933 590148964499587893326917 := by
  unfold tailWord_3447933
  simp only [CollatzResearch.WordTrace]
  refine ⟨125756447817735075919964453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83837631878490050613309635 125756447817735075919964453)
  ·
    refine ⟨23579333965825326734993335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125756447817735075919964453 23579333965825326734993335)
    ·
      refine ⟨35369000948737990102490003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23579333965825326734993335 35369000948737990102490003)
      ·
        refine ⟨53053501423106985153735005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35369000948737990102490003 53053501423106985153735005)
        ·
          refine ⟨19895063033665119432650627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53053501423106985153735005 19895063033665119432650627)
          ·
            refine ⟨29842594550497679148975941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19895063033665119432650627 29842594550497679148975941)
            ·
              refine ⟨5595486478218314840432989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29842594550497679148975941 5595486478218314840432989)
              ·
                refine ⟨2098307429331868065162371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5595486478218314840432989 2098307429331868065162371)
                ·
                  refine ⟨3147461143997802097743557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2098307429331868065162371 3147461143997802097743557)
                  ·
                    refine ⟨590148964499587893326917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3147461143997802097743557 590148964499587893326917)
                    ·
                      rfl

theorem cell23_3447933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 3, 1, 4].length) (baseStart_3447933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3447933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3447933 prefixEnd_3447933 := by exact prefixLift 3447933
  have htrace : WordTrace (prefixWord ++ tailWord_3447933) baseStart_3447933 baseEnd_3447933 := by
    simpa [prefixWord, tailWord_3447933, baseEnd_3447933] using wordTrace_append hprefix tailTrace_3447933
  have hstable : (prefixWord ++ tailWord_3447933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447933).length < 2 ^ (prefixWord ++ tailWord_3447933).sum := by decide
  have hdescent : baseEnd_3447933 < baseStart_3447933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447952 : List Nat := [2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 7]
def baseStart_3447952 : Nat := 118140960795 + 3447952 * 2 ^ 59
def prefixEnd_3447952 : Nat := 4983230072969 + 3 ^ 40 * 3447952 * 2
def baseEnd_3447952 : Nat := 1770456649631199105643163

theorem tailTrace_3447952 : CollatzResearch.WordTrace tailWord_3447952 prefixEnd_3447952 1770456649631199105643163 := by
  unfold tailWord_3447952
  simp only [CollatzResearch.WordTrace]
  refine ⟨62878570402333121082453055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83838093869777494776604073 62878570402333121082453055)
  ·
    refine ⟨94317855603499681623679583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62878570402333121082453055 94317855603499681623679583)
    ·
      refine ⟨141476783405249522435519375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94317855603499681623679583 141476783405249522435519375)
      ·
        refine ⟨212215175107874283653279063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141476783405249522435519375 212215175107874283653279063)
        ·
          refine ⟨318322762661811425479918595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212215175107874283653279063 318322762661811425479918595)
          ·
            refine ⟨477484143992717138219877893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318322762661811425479918595 477484143992717138219877893)
            ·
              refine ⟨89528276998634463416227105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 477484143992717138219877893 89528276998634463416227105)
              ·
                refine ⟨67146207748975847562170329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89528276998634463416227105 67146207748975847562170329)
                ·
                  refine ⟨50359655811731885671627747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67146207748975847562170329 50359655811731885671627747)
                  ·
                    refine ⟨75539483717597828507441621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50359655811731885671627747 75539483717597828507441621)
                    ·
                      refine ⟨1770456649631199105643163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 75539483717597828507441621 1770456649631199105643163)
                      ·
                        rfl

theorem cell23_3447952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 7].length) (baseStart_3447952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3447952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3447952 prefixEnd_3447952 := by exact prefixLift 3447952
  have htrace : WordTrace (prefixWord ++ tailWord_3447952) baseStart_3447952 baseEnd_3447952 := by
    simpa [prefixWord, tailWord_3447952, baseEnd_3447952] using wordTrace_append hprefix tailTrace_3447952
  have hstable : (prefixWord ++ tailWord_3447952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447952).length < 2 ^ (prefixWord ++ tailWord_3447952).sum := by decide
  have hdescent : baseEnd_3447952 < baseStart_3447952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3447999 : List Nat := [1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 5]
def baseStart_3447999 : Nat := 118140960795 + 3447999 * 2 ^ 59
def prefixEnd_3447999 : Nat := 4983230072969 + 3 ^ 40 * 3447999 * 2
def baseEnd_3447999 : Nat := 1770480783221960421755447

theorem tailTrace_3447999 : CollatzResearch.WordTrace tailWord_3447999 prefixEnd_3447999 1770480783221960421755447 := by
  unfold tailWord_3447999
  simp only [CollatzResearch.WordTrace]
  refine ⟨125758855035495969191867051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83839236690330646127911367 125758855035495969191867051)
  ·
    refine ⟨188638282553243953787800577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125758855035495969191867051 188638282553243953787800577)
    ·
      refine ⟨141478711914932965340850433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188638282553243953787800577 141478711914932965340850433)
      ·
        refine ⟨106109033936199724005637825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141478711914932965340850433 106109033936199724005637825)
        ·
          refine ⟨79581775452149793004228369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106109033936199724005637825 79581775452149793004228369)
          ·
            refine ⟨59686331589112344753171277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79581775452149793004228369 59686331589112344753171277)
            ·
              refine ⟨22382374345917129282439229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59686331589112344753171277 22382374345917129282439229)
              ·
                refine ⟨8393390379718923480914711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22382374345917129282439229 8393390379718923480914711)
                ·
                  refine ⟨12590085569578385221372067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8393390379718923480914711 12590085569578385221372067)
                  ·
                    refine ⟨18885128354367577832058101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12590085569578385221372067 18885128354367577832058101)
                    ·
                      refine ⟨1770480783221960421755447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18885128354367577832058101 1770480783221960421755447)
                      ·
                        rfl

theorem cell23_3447999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 5].length) (baseStart_3447999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3447999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3447999 prefixEnd_3447999 := by exact prefixLift 3447999
  have htrace : WordTrace (prefixWord ++ tailWord_3447999) baseStart_3447999 baseEnd_3447999 := by
    simpa [prefixWord, tailWord_3447999, baseEnd_3447999] using wordTrace_append hprefix tailTrace_3447999
  have hstable : (prefixWord ++ tailWord_3447999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3447999).length < 2 ^ (prefixWord ++ tailWord_3447999).sum := by decide
  have hdescent : baseEnd_3447999 < baseStart_3447999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3447999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448023 : List Nat := [1, 1, 3, 2, 1, 2, 6, 1, 2, 4]
def baseStart_3448023 : Nat := 118140960795 + 3448023 * 2 ^ 59
def prefixEnd_3448023 : Nat := 4983230072969 + 3 ^ 40 * 3448023 * 2
def baseEnd_3448023 : Nat := 590164368919222775951779

theorem tailTrace_3448023 : CollatzResearch.WordTrace tailWord_3448023 prefixEnd_3448023 590164368919222775951779 := by
  unfold tailWord_3448023
  simp only [CollatzResearch.WordTrace]
  refine ⟨125759730387409021290740723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83839820258272680860493815 125759730387409021290740723)
  ·
    refine ⟨188639595581113531936111085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125759730387409021290740723 188639595581113531936111085)
    ·
      refine ⟨70739848342917574476041657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188639595581113531936111085 70739848342917574476041657)
      ·
        refine ⟨53054886257188180857031243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70739848342917574476041657 53054886257188180857031243)
        ·
          refine ⟨79582329385782271285546865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53054886257188180857031243 79582329385782271285546865)
          ·
            refine ⟨59686747039336703464160149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79582329385782271285546865 59686747039336703464160149)
            ·
              refine ⟨2797816267468907974882507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 59686747039336703464160149 2797816267468907974882507)
              ·
                refine ⟨4196724401203361962323761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2797816267468907974882507 4196724401203361962323761)
                ·
                  refine ⟨3147543300902521471742821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4196724401203361962323761 3147543300902521471742821)
                  ·
                    refine ⟨590164368919222775951779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3147543300902521471742821 590164368919222775951779)
                    ·
                      rfl

theorem cell23_3448023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 1, 2, 4].length) (baseStart_3448023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3448023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3448023 prefixEnd_3448023 := by exact prefixLift 3448023
  have htrace : WordTrace (prefixWord ++ tailWord_3448023) baseStart_3448023 baseEnd_3448023 := by
    simpa [prefixWord, tailWord_3448023, baseEnd_3448023] using wordTrace_append hprefix tailTrace_3448023
  have hstable : (prefixWord ++ tailWord_3448023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448023).length < 2 ^ (prefixWord ++ tailWord_3448023).sum := by decide
  have hdescent : baseEnd_3448023 < baseStart_3448023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448033 : List Nat := [1, 2, 3, 1, 3, 2, 3, 2, 1, 2, 3]
def baseStart_3448033 : Nat := 118140960795 + 3448033 * 2 ^ 59
def prefixEnd_3448033 : Nat := 4983230072969 + 3 ^ 40 * 3448033 * 2
def baseEnd_3448033 : Nat := 1770498241564213288730291

theorem tailTrace_3448033 : CollatzResearch.WordTrace tailWord_3448033 prefixEnd_3448033 1770498241564213288730291 := by
  unfold tailWord_3448033
  simp only [CollatzResearch.WordTrace]
  refine ⟨125760095117372792998604753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83840063411581861999069835 125760095117372792998604753)
  ·
    refine ⟨94320071338029594748953565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125760095117372792998604753 94320071338029594748953565)
    ·
      refine ⟨35370026751761098030857587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94320071338029594748953565 35370026751761098030857587)
      ·
        refine ⟨53055040127641647046286381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35370026751761098030857587 53055040127641647046286381)
        ·
          refine ⟨19895640047865617642357393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53055040127641647046286381 19895640047865617642357393)
          ·
            refine ⟨14921730035899213231768045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19895640047865617642357393 14921730035899213231768045)
            ·
              refine ⟨5595648763462204961913017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14921730035899213231768045 5595648763462204961913017)
              ·
                refine ⟨4196736572596653721434763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5595648763462204961913017 4196736572596653721434763)
                ·
                  refine ⟨6295104858894980582152145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4196736572596653721434763 6295104858894980582152145)
                  ·
                    refine ⟨4721328644171235436614109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6295104858894980582152145 4721328644171235436614109)
                    ·
                      refine ⟨1770498241564213288730291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4721328644171235436614109 1770498241564213288730291)
                      ·
                        rfl

theorem cell23_3448033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 2, 1, 2, 3].length) (baseStart_3448033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3448033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3448033 prefixEnd_3448033 := by exact prefixLift 3448033
  have htrace : WordTrace (prefixWord ++ tailWord_3448033) baseStart_3448033 baseEnd_3448033 := by
    simpa [prefixWord, tailWord_3448033, baseEnd_3448033] using wordTrace_append hprefix tailTrace_3448033
  have hstable : (prefixWord ++ tailWord_3448033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448033).length < 2 ^ (prefixWord ++ tailWord_3448033).sum := by decide
  have hdescent : baseEnd_3448033 < baseStart_3448033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448046 : List Nat := [4, 1, 2, 1, 1, 1, 3, 1, 3, 3, 3]
def baseStart_3448046 : Nat := 118140960795 + 3448046 * 2 ^ 59
def prefixEnd_3448046 : Nat := 4983230072969 + 3 ^ 40 * 3448046 * 2
def baseEnd_3448046 : Nat := 1770504916812721737867731

theorem tailTrace_3448046 : CollatzResearch.WordTrace tailWord_3448046 prefixEnd_3448046 1770504916812721737867731 := by
  unfold tailWord_3448046
  simp only [CollatzResearch.WordTrace]
  refine ⟨15720071158290712027353499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83840379510883797479218661 15720071158290712027353499)
  ·
    refine ⟨23580106737436068041030249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15720071158290712027353499 23580106737436068041030249)
    ·
      refine ⟨17685080053077051030772687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23580106737436068041030249 17685080053077051030772687)
      ·
        refine ⟨26527620079615576546159031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17685080053077051030772687 26527620079615576546159031)
        ·
          refine ⟨39791430119423364819238547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26527620079615576546159031 39791430119423364819238547)
          ·
            refine ⟨59687145179135047228857821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39791430119423364819238547 59687145179135047228857821)
            ·
              refine ⟨22382679442175642710821683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59687145179135047228857821 22382679442175642710821683)
              ·
                refine ⟨33574019163263464066232525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22382679442175642710821683 33574019163263464066232525)
                ·
                  refine ⟨12590257186223799024837197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33574019163263464066232525 12590257186223799024837197)
                  ·
                    refine ⟨4721346444833924634313949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12590257186223799024837197 4721346444833924634313949)
                    ·
                      refine ⟨1770504916812721737867731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4721346444833924634313949 1770504916812721737867731)
                      ·
                        rfl

theorem cell23_3448046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_3448046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3448046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3448046 prefixEnd_3448046 := by exact prefixLift 3448046
  have htrace : WordTrace (prefixWord ++ tailWord_3448046) baseStart_3448046 baseEnd_3448046 := by
    simpa [prefixWord, tailWord_3448046, baseEnd_3448046] using wordTrace_append hprefix tailTrace_3448046
  have hstable : (prefixWord ++ tailWord_3448046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448046).length < 2 ^ (prefixWord ++ tailWord_3448046).sum := by decide
  have hdescent : baseEnd_3448046 < baseStart_3448046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448050 : List Nat := [3, 2, 1, 3, 4, 1, 1, 1, 1, 1, 5]
def baseStart_3448050 : Nat := 118140960795 + 3448050 * 2 ^ 59
def prefixEnd_3448050 : Nat := 4983230072969 + 3 ^ 40 * 3448050 * 2
def baseEnd_3448050 : Nat := 1770506970735339722217713

theorem tailTrace_3448050 : CollatzResearch.WordTrace tailWord_3448050 prefixEnd_3448050 1770506970735339722217713 := by
  unfold tailWord_3448050
  simp only [CollatzResearch.WordTrace]
  refine ⟨31440178789577801225493401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83840476772207469934649069 31440178789577801225493401)
  ·
    refine ⟨23580134092183350919120051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31440178789577801225493401 23580134092183350919120051)
    ·
      refine ⟨35370201138275026378680077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23580134092183350919120051 35370201138275026378680077)
      ·
        refine ⟨13263825426853134892005029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35370201138275026378680077 13263825426853134892005029)
        ·
          refine ⟨2486967267534962792250943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13263825426853134892005029 2486967267534962792250943)
          ·
            refine ⟨3730450901302444188376415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2486967267534962792250943 3730450901302444188376415)
            ·
              refine ⟨5595676351953666282564623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3730450901302444188376415 5595676351953666282564623)
              ·
                refine ⟨8393514527930499423846935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5595676351953666282564623 8393514527930499423846935)
                ·
                  refine ⟨12590271791895749135770403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8393514527930499423846935 12590271791895749135770403)
                  ·
                    refine ⟨18885407687843623703655605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12590271791895749135770403 18885407687843623703655605)
                    ·
                      refine ⟨1770506970735339722217713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18885407687843623703655605 1770506970735339722217713)
                      ·
                        rfl

theorem cell23_3448050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_3448050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3448050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3448050 prefixEnd_3448050 := by exact prefixLift 3448050
  have htrace : WordTrace (prefixWord ++ tailWord_3448050) baseStart_3448050 baseEnd_3448050 := by
    simpa [prefixWord, tailWord_3448050, baseEnd_3448050] using wordTrace_append hprefix tailTrace_3448050
  have hstable : (prefixWord ++ tailWord_3448050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448050).length < 2 ^ (prefixWord ++ tailWord_3448050).sum := by decide
  have hdescent : baseEnd_3448050 < baseStart_3448050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448063 : List Nat := [1, 1, 2, 2, 1, 5, 1, 4, 2, 1, 3]
def baseStart_3448063 : Nat := 118140960795 + 3448063 * 2 ^ 59
def prefixEnd_3448063 : Nat := 4983230072969 + 3 ^ 40 * 3448063 * 2
def baseEnd_3448063 : Nat := 1770513645983848171355153

theorem tailTrace_3448063 : CollatzResearch.WordTrace tailWord_3448063 prefixEnd_3448063 1770513645983848171355153 := by
  unfold tailWord_3448063
  simp only [CollatzResearch.WordTrace]
  refine ⟨125761189307264108122196843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83840792871509405414797895 125761189307264108122196843)
  ·
    refine ⟨188641783960896162183295265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125761189307264108122196843 188641783960896162183295265)
    ·
      refine ⟨141481337970672121637471449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188641783960896162183295265 141481337970672121637471449)
      ·
        refine ⟨106111003478004091228103587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141481337970672121637471449 106111003478004091228103587)
        ·
          refine ⟨159166505217006136842155381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106111003478004091228103587 159166505217006136842155381)
          ·
            refine ⟨14921859864094325328952067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 159166505217006136842155381 14921859864094325328952067)
            ·
              refine ⟨22382789796141487993428101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14921859864094325328952067 22382789796141487993428101)
              ·
                refine ⟨4196773086776528998767769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22382789796141487993428101 4196773086776528998767769)
                ·
                  refine ⟨3147579815082396749075827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4196773086776528998767769 3147579815082396749075827)
                  ·
                    refine ⟨4721369722623595123613741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3147579815082396749075827 4721369722623595123613741)
                    ·
                      refine ⟨1770513645983848171355153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4721369722623595123613741 1770513645983848171355153)
                      ·
                        rfl

theorem cell23_3448063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 4, 2, 1, 3].length) (baseStart_3448063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3448063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3448063 prefixEnd_3448063 := by exact prefixLift 3448063
  have htrace : WordTrace (prefixWord ++ tailWord_3448063) baseStart_3448063 baseEnd_3448063 := by
    simpa [prefixWord, tailWord_3448063, baseEnd_3448063] using wordTrace_append hprefix tailTrace_3448063
  have hstable : (prefixWord ++ tailWord_3448063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448063).length < 2 ^ (prefixWord ++ tailWord_3448063).sum := by decide
  have hdescent : baseEnd_3448063 < baseStart_3448063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448069 : List Nat := [1, 3, 1, 1, 2, 1, 3, 1, 1, 5, 4]
def baseStart_3448069 : Nat := 118140960795 + 3448069 * 2 ^ 59
def prefixEnd_3448069 : Nat := 4983230072969 + 3 ^ 40 * 3448069 * 2
def baseEnd_3448069 : Nat := 1770516726867775147880125

theorem tailTrace_3448069 : CollatzResearch.WordTrace tailWord_3448069 prefixEnd_3448069 1770516726867775147880125 := by
  unfold tailWord_3448069
  simp only [CollatzResearch.WordTrace]
  refine ⟨125761408145242371146915261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83840938763494914097943507 125761408145242371146915261)
  ·
    refine ⟨47160528054465889180093223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125761408145242371146915261 47160528054465889180093223)
    ·
      refine ⟨70740792081698833770139835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47160528054465889180093223 70740792081698833770139835)
      ·
        refine ⟨106111188122548250655209753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70740792081698833770139835 106111188122548250655209753)
        ·
          refine ⟨79583391091911187991407315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106111188122548250655209753 79583391091911187991407315)
          ·
            refine ⟨119375086637866781987110973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79583391091911187991407315 119375086637866781987110973)
            ·
              refine ⟨44765657489200043245166615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119375086637866781987110973 44765657489200043245166615)
              ·
                refine ⟨67148486233800064867749923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44765657489200043245166615 67148486233800064867749923)
                ·
                  refine ⟨100722729350700097301624885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67148486233800064867749923 100722729350700097301624885)
                  ·
                    refine ⟨9442755876628134122027333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 100722729350700097301624885 9442755876628134122027333)
                    ·
                      refine ⟨1770516726867775147880125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9442755876628134122027333 1770516726867775147880125)
                      ·
                        rfl

theorem cell23_3448069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 5, 4].length) (baseStart_3448069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3448069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3448069 prefixEnd_3448069 := by exact prefixLift 3448069
  have htrace : WordTrace (prefixWord ++ tailWord_3448069) baseStart_3448069 baseEnd_3448069 := by
    simpa [prefixWord, tailWord_3448069, baseEnd_3448069] using wordTrace_append hprefix tailTrace_3448069
  have hstable : (prefixWord ++ tailWord_3448069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448069).length < 2 ^ (prefixWord ++ tailWord_3448069).sum := by decide
  have hdescent : baseEnd_3448069 < baseStart_3448069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448157 : List Nat := [1, 4, 5, 1, 1, 1, 1, 1, 2, 1, 5]
def baseStart_3448157 : Nat := 118140960795 + 3448157 * 2 ^ 59
def prefixEnd_3448157 : Nat := 4983230072969 + 3 ^ 40 * 3448157 * 2
def baseEnd_3448157 : Nat := 1770561913165370803579721

theorem tailTrace_3448157 : CollatzResearch.WordTrace tailWord_3448157 prefixEnd_3448157 1770561913165370803579721 := by
  unfold tailWord_3448157
  simp only [CollatzResearch.WordTrace]
  refine ⟨125764617768923562176118725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83843078512615708117412483 125764617768923562176118725)
  ·
    refine ⟨23580865831673167908022261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125764617768923562176118725 23580865831673167908022261)
    ·
      refine ⟨2210706171719359491377087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23580865831673167908022261 2210706171719359491377087)
      ·
        refine ⟨3316059257579039237065631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2210706171719359491377087 3316059257579039237065631)
        ·
          refine ⟨4974088886368558855598447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3316059257579039237065631 4974088886368558855598447)
          ·
            refine ⟨7461133329552838283397671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4974088886368558855598447 7461133329552838283397671)
            ·
              refine ⟨11191699994329257425096507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7461133329552838283397671 11191699994329257425096507)
              ·
                refine ⟨16787549991493886137644761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11191699994329257425096507 16787549991493886137644761)
                ·
                  refine ⟨12590662493620414603233571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16787549991493886137644761 12590662493620414603233571)
                  ·
                    refine ⟨18885993740430621904850357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12590662493620414603233571 18885993740430621904850357)
                    ·
                      refine ⟨1770561913165370803579721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18885993740430621904850357 1770561913165370803579721)
                      ·
                        rfl

theorem cell23_3448157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_3448157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3448157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3448157 prefixEnd_3448157 := by exact prefixLift 3448157
  have htrace : WordTrace (prefixWord ++ tailWord_3448157) baseStart_3448157 baseEnd_3448157 := by
    simpa [prefixWord, tailWord_3448157, baseEnd_3448157] using wordTrace_append hprefix tailTrace_3448157
  have hstable : (prefixWord ++ tailWord_3448157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448157).length < 2 ^ (prefixWord ++ tailWord_3448157).sum := by decide
  have hdescent : baseEnd_3448157 < baseStart_3448157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448160 : List Nat := [2, 1, 1, 3, 4, 3, 1, 3, 5]
def baseStart_3448160 : Nat := 118140960795 + 3448160 * 2 ^ 59
def prefixEnd_3448160 : Nat := 4983230072969 + 3 ^ 40 * 3448160 * 2
def baseEnd_3448160 : Nat := 196729272623037143538023

theorem tailTrace_3448160 : CollatzResearch.WordTrace tailWord_3448160 prefixEnd_3448160 196729272623037143538023 := by
  unfold tailWord_3448160
  simp only [CollatzResearch.WordTrace]
  refine ⟨62882363593956346844238967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83843151458608462458985289 62882363593956346844238967)
  ·
    refine ⟨94323545390934520266358451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62882363593956346844238967 94323545390934520266358451)
    ·
      refine ⟨141485318086401780399537677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94323545390934520266358451 141485318086401780399537677)
      ·
        refine ⟨53056994282400667649826629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141485318086401780399537677 53056994282400667649826629)
        ·
          refine ⟨9948186427950125184342493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53056994282400667649826629 9948186427950125184342493)
          ·
            refine ⟨3730569910481296944128435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9948186427950125184342493 3730569910481296944128435)
            ·
              refine ⟨5595854865721945416192653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3730569910481296944128435 5595854865721945416192653)
              ·
                refine ⟨2098445574645729531072245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5595854865721945416192653 2098445574645729531072245)
                ·
                  refine ⟨196729272623037143538023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2098445574645729531072245 196729272623037143538023)
                  ·
                    rfl

theorem cell23_3448160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 3, 5].length) (baseStart_3448160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3448160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3448160 prefixEnd_3448160 := by exact prefixLift 3448160
  have htrace : WordTrace (prefixWord ++ tailWord_3448160) baseStart_3448160 baseEnd_3448160 := by
    simpa [prefixWord, tailWord_3448160, baseEnd_3448160] using wordTrace_append hprefix tailTrace_3448160
  have hstable : (prefixWord ++ tailWord_3448160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448160).length < 2 ^ (prefixWord ++ tailWord_3448160).sum := by decide
  have hdescent : baseEnd_3448160 < baseStart_3448160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448173 : List Nat := [1, 5, 1, 1, 1, 4, 1, 2, 2, 5]
def baseStart_3448173 : Nat := 118140960795 + 3448173 * 2 ^ 59
def prefixEnd_3448173 : Nat := 4983230072969 + 3 ^ 40 * 3448173 * 2
def baseEnd_3448173 : Nat := 590190042951947580326549

theorem tailTrace_3448173 : CollatzResearch.WordTrace tailWord_3448173 prefixEnd_3448173 590190042951947580326549 := by
  unfold tailWord_3448173
  simp only [CollatzResearch.WordTrace]
  refine ⟨125765201336865596908701173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83843467557910397939134115 125765201336865596908701173)
  ·
    refine ⟨11790487625331149710190735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125765201336865596908701173 11790487625331149710190735)
    ·
      refine ⟨17685731437996724565286103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11790487625331149710190735 17685731437996724565286103)
      ·
        refine ⟨26528597156995086847929155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17685731437996724565286103 26528597156995086847929155)
        ·
          refine ⟨39792895735492630271893733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26528597156995086847929155 39792895735492630271893733)
          ·
            refine ⟨7461167950404868175980075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39792895735492630271893733 7461167950404868175980075)
            ·
              refine ⟨11191751925607302263970113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7461167950404868175980075 11191751925607302263970113)
              ·
                refine ⟨8393813944205476697977585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11191751925607302263970113 8393813944205476697977585)
                ·
                  refine ⟨6295360458154107523483189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8393813944205476697977585 6295360458154107523483189)
                  ·
                    refine ⟨590190042951947580326549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6295360458154107523483189 590190042951947580326549)
                    ·
                      rfl

theorem cell23_3448173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_3448173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3448173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3448173 prefixEnd_3448173 := by exact prefixLift 3448173
  have htrace : WordTrace (prefixWord ++ tailWord_3448173) baseStart_3448173 baseEnd_3448173 := by
    simpa [prefixWord, tailWord_3448173, baseEnd_3448173] using wordTrace_append hprefix tailTrace_3448173
  have hstable : (prefixWord ++ tailWord_3448173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448173).length < 2 ^ (prefixWord ++ tailWord_3448173).sum := by decide
  have hdescent : baseEnd_3448173 < baseStart_3448173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448213 : List Nat := [1, 3, 2, 1, 1, 2, 3, 3, 2, 2, 3]
def baseStart_3448213 : Nat := 118140960795 + 3448213 * 2 ^ 59
def prefixEnd_3448213 : Nat := 4983230072969 + 3 ^ 40 * 3448213 * 2
def baseEnd_3448213 : Nat := 1770590668082022584479463

theorem tailTrace_3448213 : CollatzResearch.WordTrace tailWord_3448213 prefixEnd_3448213 1770590668082022584479463 := by
  unfold tailWord_3448213
  simp only [CollatzResearch.WordTrace]
  refine ⟨125766660256720683740157293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83844440171147122493438195 125766660256720683740157293)
  ·
    refine ⟨47162497596270256402558985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125766660256720683740157293 47162497596270256402558985)
    ·
      refine ⟨35371873197202692301919239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47162497596270256402558985 35371873197202692301919239)
      ·
        refine ⟨53057809795804038452878859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35371873197202692301919239 53057809795804038452878859)
        ·
          refine ⟨79586714693706057679318289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53057809795804038452878859 79586714693706057679318289)
          ·
            refine ⟨59690036020279543259488717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79586714693706057679318289 59690036020279543259488717)
            ·
              refine ⟨22383763507604828722308269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59690036020279543259488717 22383763507604828722308269)
              ·
                refine ⟨8393911315351810770865601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22383763507604828722308269 8393911315351810770865601)
                ·
                  refine ⟨6295433486513858078149201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8393911315351810770865601 6295433486513858078149201)
                  ·
                    refine ⟨4721575114885393558611901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6295433486513858078149201 4721575114885393558611901)
                    ·
                      refine ⟨1770590668082022584479463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4721575114885393558611901 1770590668082022584479463)
                      ·
                        rfl

theorem cell23_3448213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 2, 2, 3].length) (baseStart_3448213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3448213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3448213 prefixEnd_3448213 := by exact prefixLift 3448213
  have htrace : WordTrace (prefixWord ++ tailWord_3448213) baseStart_3448213 baseEnd_3448213 := by
    simpa [prefixWord, tailWord_3448213, baseEnd_3448213] using wordTrace_append hprefix tailTrace_3448213
  have hstable : (prefixWord ++ tailWord_3448213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448213).length < 2 ^ (prefixWord ++ tailWord_3448213).sum := by decide
  have hdescent : baseEnd_3448213 < baseStart_3448213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448243 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 7, 1, 3]
def baseStart_3448243 : Nat := 118140960795 + 3448243 * 2 ^ 59
def prefixEnd_3448243 : Nat := 4983230072969 + 3 ^ 40 * 3448243 * 2
def baseEnd_3448243 : Nat := 1770606072501657467104325

theorem tailTrace_3448243 : CollatzResearch.WordTrace tailWord_3448243 prefixEnd_3448243 1770606072501657467104325 := by
  unfold tailWord_3448243
  simp only [CollatzResearch.WordTrace]
  refine ⟨125767754446611998863749383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83845169631074665909166255 125767754446611998863749383)
  ·
    refine ⟨188651631669917998295624075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125767754446611998863749383 188651631669917998295624075)
    ·
      refine ⟨282977447504876997443436113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188651631669917998295624075 282977447504876997443436113)
      ·
        refine ⟨212233085628657748082577085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282977447504876997443436113 212233085628657748082577085)
        ·
          refine ⟨79587407110746655530966407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212233085628657748082577085 79587407110746655530966407)
          ·
            refine ⟨119381110666119983296449611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79587407110746655530966407 119381110666119983296449611)
            ·
              refine ⟨179071665999179974944674417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119381110666119983296449611 179071665999179974944674417)
              ·
                refine ⟨134303749499384981208505813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179071665999179974944674417 134303749499384981208505813)
                ·
                  refine ⟨3147744128891835497074355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 134303749499384981208505813 3147744128891835497074355)
                  ·
                    refine ⟨4721616193337753245611533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3147744128891835497074355 4721616193337753245611533)
                    ·
                      refine ⟨1770606072501657467104325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4721616193337753245611533 1770606072501657467104325)
                      ·
                        rfl

theorem cell23_3448243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 7, 1, 3].length) (baseStart_3448243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3448243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3448243 prefixEnd_3448243 := by exact prefixLift 3448243
  have htrace : WordTrace (prefixWord ++ tailWord_3448243) baseStart_3448243 baseEnd_3448243 := by
    simpa [prefixWord, tailWord_3448243, baseEnd_3448243] using wordTrace_append hprefix tailTrace_3448243
  have hstable : (prefixWord ++ tailWord_3448243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448243).length < 2 ^ (prefixWord ++ tailWord_3448243).sum := by decide
  have hdescent : baseEnd_3448243 < baseStart_3448243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448258 : List Nat := [3, 5, 2, 1, 2, 1, 1, 1, 2, 5]
def baseStart_3448258 : Nat := 118140960795 + 3448258 * 2 ^ 59
def prefixEnd_3448258 : Nat := 4983230072969 + 3 ^ 40 * 3448258 * 2
def baseEnd_3448258 : Nat := 590204591570491636138919

theorem tailTrace_3448258 : CollatzResearch.WordTrace tailWord_3448258 prefixEnd_3448258 590204591570491636138919 := by
  unfold tailWord_3448258
  simp only [CollatzResearch.WordTrace]
  refine ⟨31442075385389414106386357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83845534361038437617030285 31442075385389414106386357)
  ·
    refine ⟨2947694567380257572473721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31442075385389414106386357 2947694567380257572473721)
    ·
      refine ⟨2210770925535193179355291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2947694567380257572473721 2210770925535193179355291)
      ·
        refine ⟨3316156388302789769032937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2210770925535193179355291 3316156388302789769032937)
        ·
          refine ⟨2487117291227092326774703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3316156388302789769032937 2487117291227092326774703)
          ·
            refine ⟨3730675936840638490162055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2487117291227092326774703 3730675936840638490162055)
            ·
              refine ⟨5596013905260957735243083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3730675936840638490162055 5596013905260957735243083)
              ·
                refine ⟨8394020857891436602864625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5596013905260957735243083 8394020857891436602864625)
                ·
                  refine ⟨6295515643418577452148469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8394020857891436602864625 6295515643418577452148469)
                  ·
                    refine ⟨590204591570491636138919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6295515643418577452148469 590204591570491636138919)
                    ·
                      rfl

theorem cell23_3448258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_3448258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3448258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3448258 prefixEnd_3448258 := by exact prefixLift 3448258
  have htrace : WordTrace (prefixWord ++ tailWord_3448258) baseStart_3448258 baseEnd_3448258 := by
    simpa [prefixWord, tailWord_3448258, baseEnd_3448258] using wordTrace_append hprefix tailTrace_3448258
  have hstable : (prefixWord ++ tailWord_3448258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448258).length < 2 ^ (prefixWord ++ tailWord_3448258).sum := by decide
  have hdescent : baseEnd_3448258 < baseStart_3448258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448263 : List Nat := [1, 1, 4, 1, 1, 3, 2, 4, 1, 5]
def baseStart_3448263 : Nat := 118140960795 + 3448263 * 2 ^ 59
def prefixEnd_3448263 : Nat := 4983230072969 + 3 ^ 40 * 3448263 * 2
def baseEnd_3448263 : Nat := 590205447371582462951411

theorem tailTrace_3448263 : CollatzResearch.WordTrace tailWord_3448263 prefixEnd_3448263 590205447371582462951411 := by
  unfold tailWord_3448263
  simp only [CollatzResearch.WordTrace]
  refine ⟨125768483906539542279477443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83845655937693028186318295 125768483906539542279477443)
  ·
    refine ⟨188652725859809313419216165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125768483906539542279477443 188652725859809313419216165)
    ·
      refine ⟨35372386098714246266103031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188652725859809313419216165 35372386098714246266103031)
      ·
        refine ⟨53058579148071369399154547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35372386098714246266103031 53058579148071369399154547)
        ·
          refine ⟨79587868722107054098731821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53058579148071369399154547 79587868722107054098731821)
          ·
            refine ⟨29845450770790145287024433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79587868722107054098731821 29845450770790145287024433)
            ·
              refine ⟨22384088078092608965268325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29845450770790145287024433 22384088078092608965268325)
              ·
                refine ⟨4197016514642364180987811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22384088078092608965268325 4197016514642364180987811)
                ·
                  refine ⟨6295524771963546271481717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4197016514642364180987811 6295524771963546271481717)
                  ·
                    refine ⟨590205447371582462951411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6295524771963546271481717 590205447371582462951411)
                    ·
                      rfl

theorem cell23_3448263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 4, 1, 5].length) (baseStart_3448263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3448263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3448263 prefixEnd_3448263 := by exact prefixLift 3448263
  have htrace : WordTrace (prefixWord ++ tailWord_3448263) baseStart_3448263 baseEnd_3448263 := by
    simpa [prefixWord, tailWord_3448263, baseEnd_3448263] using wordTrace_append hprefix tailTrace_3448263
  have hstable : (prefixWord ++ tailWord_3448263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448263).length < 2 ^ (prefixWord ++ tailWord_3448263).sum := by decide
  have hdescent : baseEnd_3448263 < baseStart_3448263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448280 : List Nat := [2, 1, 2, 2, 2, 1, 6, 1, 1, 5]
def baseStart_3448280 : Nat := 118140960795 + 3448280 * 2 ^ 59
def prefixEnd_3448280 : Nat := 4983230072969 + 3 ^ 40 * 3448280 * 2
def baseEnd_3448280 : Nat := 590208357095291274113885

theorem tailTrace_3448280 : CollatzResearch.WordTrace tailWord_3448280 prefixEnd_3448280 590208357095291274113885 := by
  unfold tailWord_3448280
  simp only [CollatzResearch.WordTrace]
  refine ⟨62884551973738977091423147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83846069298318636121897529 62884551973738977091423147)
  ·
    refine ⟨94326827960608465637134721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62884551973738977091423147 94326827960608465637134721)
    ·
      refine ⟨70745120970456349227851041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94326827960608465637134721 70745120970456349227851041)
      ·
        refine ⟨53058840727842261920888281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70745120970456349227851041 53058840727842261920888281)
        ·
          refine ⟨39794130545881696440666211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53058840727842261920888281 39794130545881696440666211)
          ·
            refine ⟨59691195818822544660999317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39794130545881696440666211 59691195818822544660999317)
            ·
              refine ⟨2798024804007306780984343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 59691195818822544660999317 2798024804007306780984343)
              ·
                refine ⟨4197037206010960171476515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2798024804007306780984343 4197037206010960171476515)
                ·
                  refine ⟨6295555809016440257214773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4197037206010960171476515 6295555809016440257214773)
                  ·
                    refine ⟨590208357095291274113885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6295555809016440257214773 590208357095291274113885)
                    ·
                      rfl

theorem cell23_3448280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 1, 1, 5].length) (baseStart_3448280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3448280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3448280 prefixEnd_3448280 := by exact prefixLift 3448280
  have htrace : WordTrace (prefixWord ++ tailWord_3448280) baseStart_3448280 baseEnd_3448280 := by
    simpa [prefixWord, tailWord_3448280, baseEnd_3448280] using wordTrace_append hprefix tailTrace_3448280
  have hstable : (prefixWord ++ tailWord_3448280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448280).length < 2 ^ (prefixWord ++ tailWord_3448280).sum := by decide
  have hdescent : baseEnd_3448280 < baseStart_3448280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448303 : List Nat := [1, 1, 2, 1, 4, 1, 2, 1, 5, 2, 3]
def baseStart_3448303 : Nat := 118140960795 + 3448303 * 2 ^ 59
def prefixEnd_3448303 : Nat := 4983230072969 + 3 ^ 40 * 3448303 * 2
def baseEnd_3448303 : Nat := 1770636881340927232354049

theorem tailTrace_3448303 : CollatzResearch.WordTrace tailWord_3448303 prefixEnd_3448303 1770636881340927232354049 := by
  unfold tailWord_3448303
  simp only [CollatzResearch.WordTrace]
  refine ⟨125769942826394629110933563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83846628550929752740622375 125769942826394629110933563)
  ·
    refine ⟨188654914239591943666400345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125769942826394629110933563 188654914239591943666400345)
    ·
      refine ⟨141491185679693957749800259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188654914239591943666400345 141491185679693957749800259)
      ·
        refine ⟨212236778519540936624700389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141491185679693957749800259 212236778519540936624700389)
        ·
          refine ⟨39794395972413925617131323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212236778519540936624700389 39794395972413925617131323)
          ·
            refine ⟨59691593958620888425696985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39794395972413925617131323 59691593958620888425696985)
            ·
              refine ⟨44768695468965666319272739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59691593958620888425696985 44768695468965666319272739)
              ·
                refine ⟨67153043203448499478909109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44768695468965666319272739 67153043203448499478909109)
                ·
                  refine ⟨6295597800323296826147729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67153043203448499478909109 6295597800323296826147729)
                  ·
                    refine ⟨4721698350242472619610797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6295597800323296826147729 4721698350242472619610797)
                    ·
                      refine ⟨1770636881340927232354049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4721698350242472619610797 1770636881340927232354049)
                      ·
                        rfl

theorem cell23_3448303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 5, 2, 3].length) (baseStart_3448303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3448303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3448303 prefixEnd_3448303 := by exact prefixLift 3448303
  have htrace : WordTrace (prefixWord ++ tailWord_3448303) baseStart_3448303 baseEnd_3448303 := by
    simpa [prefixWord, tailWord_3448303, baseEnd_3448303] using wordTrace_append hprefix tailTrace_3448303
  have hstable : (prefixWord ++ tailWord_3448303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448303).length < 2 ^ (prefixWord ++ tailWord_3448303).sum := by decide
  have hdescent : baseEnd_3448303 < baseStart_3448303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448310 : List Nat := [5, 1, 1, 1, 2, 2, 3, 1, 1, 6]
def baseStart_3448310 : Nat := 118140960795 + 3448310 * 2 ^ 59
def prefixEnd_3448310 : Nat := 4983230072969 + 3 ^ 40 * 3448310 * 2
def baseEnd_3448310 : Nat := 590213491901836234988839

theorem tailTrace_3448310 : CollatzResearch.WordTrace tailWord_3448310 prefixEnd_3448310 590213491901836234988839 := by
  unfold tailWord_3448310
  simp only [CollatzResearch.WordTrace]
  refine ⟨7860637383585579331652399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83846798758246179537625589 7860637383585579331652399)
  ·
    refine ⟨11790956075378368997478599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7860637383585579331652399 11790956075378368997478599)
    ·
      refine ⟨17686434113067553496217899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11790956075378368997478599 17686434113067553496217899)
      ·
        refine ⟨26529651169601330244326849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17686434113067553496217899 26529651169601330244326849)
        ·
          refine ⟨19897238377200997683245137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26529651169601330244326849 19897238377200997683245137)
          ·
            refine ⟨14922928782900748262433853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19897238377200997683245137 14922928782900748262433853)
            ·
              refine ⟨5596098293587780598412695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14922928782900748262433853 5596098293587780598412695)
              ·
                refine ⟨8394147440381670897619043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5596098293587780598412695 8394147440381670897619043)
                ·
                  refine ⟨12591221160572506346428565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8394147440381670897619043 12591221160572506346428565)
                  ·
                    refine ⟨590213491901836234988839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12591221160572506346428565 590213491901836234988839)
                    ·
                      rfl

theorem cell23_3448310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_3448310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3448310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3448310 prefixEnd_3448310 := by exact prefixLift 3448310
  have htrace : WordTrace (prefixWord ++ tailWord_3448310) baseStart_3448310 baseEnd_3448310 := by
    simpa [prefixWord, tailWord_3448310, baseEnd_3448310] using wordTrace_append hprefix tailTrace_3448310
  have hstable : (prefixWord ++ tailWord_3448310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448310).length < 2 ^ (prefixWord ++ tailWord_3448310).sum := by decide
  have hdescent : baseEnd_3448310 < baseStart_3448310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448317 : List Nat := [1, 4, 1, 1, 1, 4, 2, 2, 3, 2, 2]
def baseStart_3448317 : Nat := 118140960795 + 3448317 * 2 ^ 59
def prefixEnd_3448317 : Nat := 4983230072969 + 3 ^ 40 * 3448317 * 2
def baseEnd_3448317 : Nat := 1770644070070090177578985

theorem tailTrace_3448317 : CollatzResearch.WordTrace tailWord_3448317 prefixEnd_3448317 1770644070070090177578985 := by
  unfold tailWord_3448317
  simp only [CollatzResearch.WordTrace]
  refine ⟨125770453448343909501943205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83846968965562606334628803 125770453448343909501943205)
  ·
    refine ⟨23581960021564483031614351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125770453448343909501943205 23581960021564483031614351)
    ·
      refine ⟨35372940032346724547421527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23581960021564483031614351 35372940032346724547421527)
      ·
        refine ⟨53059410048520086821132291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35372940032346724547421527 53059410048520086821132291)
        ·
          refine ⟨79589115072780130231698437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53059410048520086821132291 79589115072780130231698437)
          ·
            refine ⟨14922959076146274418443457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79589115072780130231698437 14922959076146274418443457)
            ·
              refine ⟨11192219307109705813832593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14922959076146274418443457 11192219307109705813832593)
              ·
                refine ⟨8394164480332279360374445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11192219307109705813832593 8394164480332279360374445)
                ·
                  refine ⟨3147811680124604760140417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8394164480332279360374445 3147811680124604760140417)
                  ·
                    refine ⟨2360858760093453570105313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3147811680124604760140417 2360858760093453570105313)
                    ·
                      refine ⟨1770644070070090177578985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2360858760093453570105313 1770644070070090177578985)
                      ·
                        rfl

theorem cell23_3448317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 3, 2, 2].length) (baseStart_3448317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3448317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3448317 prefixEnd_3448317 := by exact prefixLift 3448317
  have htrace : WordTrace (prefixWord ++ tailWord_3448317) baseStart_3448317 baseEnd_3448317 := by
    simpa [prefixWord, tailWord_3448317, baseEnd_3448317] using wordTrace_append hprefix tailTrace_3448317
  have hstable : (prefixWord ++ tailWord_3448317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448317).length < 2 ^ (prefixWord ++ tailWord_3448317).sum := by decide
  have hdescent : baseEnd_3448317 < baseStart_3448317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448377 : List Nat := [1, 2, 1, 5, 1, 3, 1, 1, 3, 3, 2]
def baseStart_3448377 : Nat := 118140960795 + 3448377 * 2 ^ 59
def prefixEnd_3448377 : Nat := 4983230072969 + 3 ^ 40 * 3448377 * 2
def baseEnd_3448377 : Nat := 1770674878909359942828709

theorem tailTrace_3448377 : CollatzResearch.WordTrace tailWord_3448377 prefixEnd_3448377 1770674878909359942828709 := by
  unfold tailWord_3448377
  simp only [CollatzResearch.WordTrace]
  refine ⟨125772641828126539749127385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83848427885417693166084923 125772641828126539749127385)
  ·
    refine ⟨94329481371094904811845539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125772641828126539749127385 94329481371094904811845539)
    ·
      refine ⟨141494222056642357217768309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94329481371094904811845539 141494222056642357217768309)
      ·
        refine ⟨13265083317810220989165779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 141494222056642357217768309 13265083317810220989165779)
        ·
          refine ⟨19897624976715331483748669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13265083317810220989165779 19897624976715331483748669)
          ·
            refine ⟨7461609366268249306405751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19897624976715331483748669 7461609366268249306405751)
            ·
              refine ⟨11192414049402373959608627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7461609366268249306405751 11192414049402373959608627)
              ·
                refine ⟨16788621074103560939412941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11192414049402373959608627 16788621074103560939412941)
                ·
                  refine ⟨6295732902788835352279853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16788621074103560939412941 6295732902788835352279853)
                  ·
                    refine ⟨2360899838545813257104945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6295732902788835352279853 2360899838545813257104945)
                    ·
                      refine ⟨1770674878909359942828709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2360899838545813257104945 1770674878909359942828709)
                      ·
                        rfl

theorem cell23_3448377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_3448377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3448377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3448377 prefixEnd_3448377 := by exact prefixLift 3448377
  have htrace : WordTrace (prefixWord ++ tailWord_3448377) baseStart_3448377 baseEnd_3448377 := by
    simpa [prefixWord, tailWord_3448377, baseEnd_3448377] using wordTrace_append hprefix tailTrace_3448377
  have hstable : (prefixWord ++ tailWord_3448377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448377).length < 2 ^ (prefixWord ++ tailWord_3448377).sum := by decide
  have hdescent : baseEnd_3448377 < baseStart_3448377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448393 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 4, 4, 3]
def baseStart_3448393 : Nat := 118140960795 + 3448393 * 2 ^ 59
def prefixEnd_3448393 : Nat := 4983230072969 + 3 ^ 40 * 3448393 * 2
def baseEnd_3448393 : Nat := 1770683094599831880228635

theorem tailTrace_3448393 : CollatzResearch.WordTrace tailWord_3448393 prefixEnd_3448393 1770683094599831880228635 := by
  unfold tailWord_3448393
  simp only [CollatzResearch.WordTrace]
  refine ⟨125773225396068574481709833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83848816930712382987806555 125773225396068574481709833)
  ·
    refine ⟨94329919047051430861282375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125773225396068574481709833 94329919047051430861282375)
    ·
      refine ⟨141494878570577146291923563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94329919047051430861282375 141494878570577146291923563)
      ·
        refine ⟨212242317855865719437885345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141494878570577146291923563 212242317855865719437885345)
        ·
          refine ⟨159181738391899289578414009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212242317855865719437885345 159181738391899289578414009)
          ·
            refine ⟨119386303793924467183810507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159181738391899289578414009 119386303793924467183810507)
            ·
              refine ⟨179079455690886700775715761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119386303793924467183810507 179079455690886700775715761)
              ·
                refine ⟨134309591768165025581786821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179079455690886700775715761 134309591768165025581786821)
                ·
                  refine ⟨25183048456530942296585029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 134309591768165025581786821 25183048456530942296585029)
                  ·
                    refine ⟨4721821585599551680609693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25183048456530942296585029 4721821585599551680609693)
                    ·
                      refine ⟨1770683094599831880228635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4721821585599551680609693 1770683094599831880228635)
                      ·
                        rfl

theorem cell23_3448393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 4, 3].length) (baseStart_3448393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3448393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3448393 prefixEnd_3448393 := by exact prefixLift 3448393
  have htrace : WordTrace (prefixWord ++ tailWord_3448393) baseStart_3448393 baseEnd_3448393 := by
    simpa [prefixWord, tailWord_3448393, baseEnd_3448393] using wordTrace_append hprefix tailTrace_3448393
  have hstable : (prefixWord ++ tailWord_3448393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448393).length < 2 ^ (prefixWord ++ tailWord_3448393).sum := by decide
  have hdescent : baseEnd_3448393 < baseStart_3448393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448394 : List Nat := [3, 1, 2, 1, 1, 3, 5, 1, 1, 3, 2]
def baseStart_3448394 : Nat := 118140960795 + 3448394 * 2 ^ 59
def prefixEnd_3448394 : Nat := 4983230072969 + 3 ^ 40 * 3448394 * 2
def baseEnd_3448394 : Nat := 1770683608080486376316131

theorem tailTrace_3448394 : CollatzResearch.WordTrace tailWord_3448394 prefixEnd_3448394 1770683608080486376316131 := by
  unfold tailWord_3448394
  simp only [CollatzResearch.WordTrace]
  refine ⟨31443315467266237913124059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83848841246043301101664157 31443315467266237913124059)
  ·
    refine ⟨47164973200899356869686089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31443315467266237913124059 47164973200899356869686089)
    ·
      refine ⟨35373729900674517652264567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47164973200899356869686089 35373729900674517652264567)
      ·
        refine ⟨53060594851011776478396851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35373729900674517652264567 53060594851011776478396851)
        ·
          refine ⟨79590892276517664717595277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53060594851011776478396851 79590892276517664717595277)
          ·
            refine ⟨29846584603694124269098229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79590892276517664717595277 29846584603694124269098229)
            ·
              refine ⟨2798117306596324150227959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29846584603694124269098229 2798117306596324150227959)
              ·
                refine ⟨4197175959894486225341939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2798117306596324150227959 4197175959894486225341939)
                ·
                  refine ⟨6295763939841729338012909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4197175959894486225341939 6295763939841729338012909)
                  ·
                    refine ⟨2360911477440648501754841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6295763939841729338012909 2360911477440648501754841)
                    ·
                      refine ⟨1770683608080486376316131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2360911477440648501754841 1770683608080486376316131)
                      ·
                        rfl

theorem cell23_3448394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 1, 1, 3, 2].length) (baseStart_3448394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3448394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3448394 prefixEnd_3448394 := by exact prefixLift 3448394
  have htrace : WordTrace (prefixWord ++ tailWord_3448394) baseStart_3448394 baseEnd_3448394 := by
    simpa [prefixWord, tailWord_3448394, baseEnd_3448394] using wordTrace_append hprefix tailTrace_3448394
  have hstable : (prefixWord ++ tailWord_3448394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448394).length < 2 ^ (prefixWord ++ tailWord_3448394).sum := by decide
  have hdescent : baseEnd_3448394 < baseStart_3448394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448420 : List Nat := [2, 3, 1, 1, 2, 4, 1, 1, 2, 2, 4]
def baseStart_3448420 : Nat := 118140960795 + 3448420 * 2 ^ 59
def prefixEnd_3448420 : Nat := 4983230072969 + 3 ^ 40 * 3448420 * 2
def baseEnd_3448420 : Nat := 1770696958577503274591011

theorem tailTrace_3448420 : CollatzResearch.WordTrace tailWord_3448420 prefixEnd_3448420 1770696958577503274591011 := by
  unfold tailWord_3448420
  simp only [CollatzResearch.WordTrace]
  refine ⟨62887105083485379046471357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83849473444647172061961809 62887105083485379046471357)
  ·
    refine ⟨23582664406307017142426759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62887105083485379046471357 23582664406307017142426759)
    ·
      refine ⟨35373996609460525713640139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23582664406307017142426759 35373996609460525713640139)
      ·
        refine ⟨53060994914190788570460209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35373996609460525713640139 53060994914190788570460209)
        ·
          refine ⟨39795746185643091427845157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53060994914190788570460209 39795746185643091427845157)
          ·
            refine ⟨7461702409808079642720967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39795746185643091427845157 7461702409808079642720967)
            ·
              refine ⟨11192553614712119464081451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7461702409808079642720967 11192553614712119464081451)
              ·
                refine ⟨16788830422068179196122177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11192553614712119464081451 16788830422068179196122177)
                ·
                  refine ⟨12591622816551134397091633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16788830422068179196122177 12591622816551134397091633)
                  ·
                    refine ⟨9443717112413350797818725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12591622816551134397091633 9443717112413350797818725)
                    ·
                      refine ⟨1770696958577503274591011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9443717112413350797818725 1770696958577503274591011)
                      ·
                        rfl

theorem cell23_3448420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_3448420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3448420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3448420 prefixEnd_3448420 := by exact prefixLift 3448420
  have htrace : WordTrace (prefixWord ++ tailWord_3448420) baseStart_3448420 baseEnd_3448420 := by
    simpa [prefixWord, tailWord_3448420, baseEnd_3448420] using wordTrace_append hprefix tailTrace_3448420
  have hstable : (prefixWord ++ tailWord_3448420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448420).length < 2 ^ (prefixWord ++ tailWord_3448420).sum := by decide
  have hdescent : baseEnd_3448420 < baseStart_3448420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448424 : List Nat := [2, 1, 4, 3, 1, 2, 2, 1, 1, 4, 2]
def baseStart_3448424 : Nat := 118140960795 + 3448424 * 2 ^ 59
def prefixEnd_3448424 : Nat := 4983230072969 + 3 ^ 40 * 3448424 * 2
def baseEnd_3448424 : Nat := 1770699012500121258940993

theorem tailTrace_3448424 : CollatzResearch.WordTrace tailWord_3448424 prefixEnd_3448424 1770699012500121258940993 := by
  unfold tailWord_3448424
  simp only [CollatzResearch.WordTrace]
  refine ⟨62887178029478133388044163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83849570705970844517392217 62887178029478133388044163)
  ·
    refine ⟨94330767044217200082066245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62887178029478133388044163 94330767044217200082066245)
    ·
      refine ⟨17687018820790725015387421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94330767044217200082066245 17687018820790725015387421)
      ·
        refine ⟨6632632057796521880770283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17687018820790725015387421 6632632057796521880770283)
        ·
          refine ⟨9948948086694782821155425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6632632057796521880770283 9948948086694782821155425)
          ·
            refine ⟨7461711065021087115866569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9948948086694782821155425 7461711065021087115866569)
            ·
              refine ⟨5596283298765815336899927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7461711065021087115866569 5596283298765815336899927)
              ·
                refine ⟨8394424948148723005349891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5596283298765815336899927 8394424948148723005349891)
                ·
                  refine ⟨12591637422223084508024837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8394424948148723005349891 12591637422223084508024837)
                  ·
                    refine ⟨2360932016666828345254657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12591637422223084508024837 2360932016666828345254657)
                    ·
                      refine ⟨1770699012500121258940993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2360932016666828345254657 1770699012500121258940993)
                      ·
                        rfl

theorem cell23_3448424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_3448424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3448424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3448424 prefixEnd_3448424 := by exact prefixLift 3448424
  have htrace : WordTrace (prefixWord ++ tailWord_3448424) baseStart_3448424 baseEnd_3448424 := by
    simpa [prefixWord, tailWord_3448424, baseEnd_3448424] using wordTrace_append hprefix tailTrace_3448424
  have hstable : (prefixWord ++ tailWord_3448424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448424).length < 2 ^ (prefixWord ++ tailWord_3448424).sum := by decide
  have hdescent : baseEnd_3448424 < baseStart_3448424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448443 : List Nat := [1, 1, 1, 1, 1, 4, 5, 1, 1, 7]
def baseStart_3448443 : Nat := 118140960795 + 3448443 * 2 ^ 59
def prefixEnd_3448443 : Nat := 4983230072969 + 3 ^ 40 * 3448443 * 2
def baseEnd_3448443 : Nat := 590236256210852228201135

theorem tailTrace_3448443 : CollatzResearch.WordTrace tailWord_3448443 prefixEnd_3448443 590236256210852228201135 := by
  unfold tailWord_3448443
  simp only [CollatzResearch.WordTrace]
  refine ⟨125775049045887433021029983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83850032697258288680686655 125775049045887433021029983)
  ·
    refine ⟨188662573568831149531544975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125775049045887433021029983 188662573568831149531544975)
    ·
      refine ⟨282993860353246724297317463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188662573568831149531544975 282993860353246724297317463)
      ·
        refine ⟨424490790529870086445976195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282993860353246724297317463 424490790529870086445976195)
        ·
          refine ⟨636736185794805129668964293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424490790529870086445976195 636736185794805129668964293)
          ·
            refine ⟨119388034836525961812930805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 636736185794805129668964293 119388034836525961812930805)
            ·
              refine ⟨11192628265924308919962263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 119388034836525961812930805 11192628265924308919962263)
              ·
                refine ⟨16788942398886463379943395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11192628265924308919962263 16788942398886463379943395)
                ·
                  refine ⟨25183413598329695069915093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16788942398886463379943395 25183413598329695069915093)
                  ·
                    refine ⟨590236256210852228201135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25183413598329695069915093 590236256210852228201135)
                    ·
                      rfl

theorem cell23_3448443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 7].length) (baseStart_3448443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3448443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3448443 prefixEnd_3448443 := by exact prefixLift 3448443
  have htrace : WordTrace (prefixWord ++ tailWord_3448443) baseStart_3448443 baseEnd_3448443 := by
    simpa [prefixWord, tailWord_3448443, baseEnd_3448443] using wordTrace_append hprefix tailTrace_3448443
  have hstable : (prefixWord ++ tailWord_3448443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448443).length < 2 ^ (prefixWord ++ tailWord_3448443).sum := by decide
  have hdescent : baseEnd_3448443 < baseStart_3448443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448463 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 5, 3, 4]
def baseStart_3448463 : Nat := 118140960795 + 3448463 * 2 ^ 59
def prefixEnd_3448463 : Nat := 4983230072969 + 3 ^ 40 * 3448463 * 2
def baseEnd_3448463 : Nat := 1770719038245646606353313

theorem tailTrace_3448463 : CollatzResearch.WordTrace tailWord_3448463 prefixEnd_3448463 1770719038245646606353313 := by
  unfold tailWord_3448463
  simp only [CollatzResearch.WordTrace]
  refine ⟨125775778505814976436758043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83850519003876650957838695 125775778505814976436758043)
  ·
    refine ⟨188663667758722464655137065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125775778505814976436758043 188663667758722464655137065)
    ·
      refine ⟨141497750819041848491352799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188663667758722464655137065 141497750819041848491352799)
      ·
        refine ⟨212246626228562772737029199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141497750819041848491352799 212246626228562772737029199)
        ·
          refine ⟨318369939342844159105543799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212246626228562772737029199 318369939342844159105543799)
          ·
            refine ⟨477554909014266238658315699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318369939342844159105543799 477554909014266238658315699)
            ·
              refine ⟨716332363521399357987473549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 477554909014266238658315699 716332363521399357987473549)
              ·
                refine ⟨268624636320524759245302581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 716332363521399357987473549 268624636320524759245302581)
                ·
                  refine ⟨25183559655049196179247117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 268624636320524759245302581 25183559655049196179247117)
                  ·
                    refine ⟨9443834870643448567217669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25183559655049196179247117 9443834870643448567217669)
                    ·
                      refine ⟨1770719038245646606353313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9443834870643448567217669 1770719038245646606353313)
                      ·
                        rfl

theorem cell23_3448463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 3, 4].length) (baseStart_3448463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3448463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3448463 prefixEnd_3448463 := by exact prefixLift 3448463
  have htrace : WordTrace (prefixWord ++ tailWord_3448463) baseStart_3448463 baseEnd_3448463 := by
    simpa [prefixWord, tailWord_3448463, baseEnd_3448463] using wordTrace_append hprefix tailTrace_3448463
  have hstable : (prefixWord ++ tailWord_3448463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448463).length < 2 ^ (prefixWord ++ tailWord_3448463).sum := by decide
  have hdescent : baseEnd_3448463 < baseStart_3448463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448480 : List Nat := [2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 4]
def baseStart_3448480 : Nat := 118140960795 + 3448480 * 2 ^ 59
def prefixEnd_3448480 : Nat := 4983230072969 + 3 ^ 40 * 3448480 * 2
def baseEnd_3448480 : Nat := 1770727767416773039840735

theorem tailTrace_3448480 : CollatzResearch.WordTrace tailWord_3448480 prefixEnd_3448480 1770727767416773039840735 := by
  unfold tailWord_3448480
  simp only [CollatzResearch.WordTrace]
  refine ⟨62888199273376694170063447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83850932364502258893417929 62888199273376694170063447)
  ·
    refine ⟨94332298910065041255095171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62888199273376694170063447 94332298910065041255095171)
    ·
      refine ⟨141498448365097561882642757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94332298910065041255095171 141498448365097561882642757)
      ·
        refine ⟨26530959068455792852995517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141498448365097561882642757 26530959068455792852995517)
        ·
          refine ⟨9949109650670922319873319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26530959068455792852995517 9949109650670922319873319)
          ·
            refine ⟨14923664476006383479809979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9949109650670922319873319 14923664476006383479809979)
            ·
              refine ⟨22385496714009575219714969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14923664476006383479809979 22385496714009575219714969)
              ·
                refine ⟨16789122535507181414786227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22385496714009575219714969 16789122535507181414786227)
                ·
                  refine ⟨25183683803260772122179341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16789122535507181414786227 25183683803260772122179341)
                  ·
                    refine ⟨9443881426222789545817253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25183683803260772122179341 9443881426222789545817253)
                    ·
                      refine ⟨1770727767416773039840735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9443881426222789545817253 1770727767416773039840735)
                      ·
                        rfl

theorem cell23_3448480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_3448480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3448480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3448480 prefixEnd_3448480 := by exact prefixLift 3448480
  have htrace : WordTrace (prefixWord ++ tailWord_3448480) baseStart_3448480 baseEnd_3448480 := by
    simpa [prefixWord, tailWord_3448480, baseEnd_3448480] using wordTrace_append hprefix tailTrace_3448480
  have hstable : (prefixWord ++ tailWord_3448480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448480).length < 2 ^ (prefixWord ++ tailWord_3448480).sum := by decide
  have hdescent : baseEnd_3448480 < baseStart_3448480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448520 : List Nat := [2, 1, 3, 1, 2, 2, 2, 4, 6]
def baseStart_3448520 : Nat := 118140960795 + 3448520 * 2 ^ 59
def prefixEnd_3448520 : Nat := 4983230072969 + 3 ^ 40 * 3448520 * 2
def baseEnd_3448520 : Nat := 196749811849216987037839

theorem tailTrace_3448520 : CollatzResearch.WordTrace tailWord_3448520 prefixEnd_3448520 196749811849216987037839 := by
  unfold tailWord_3448520
  simp only [CollatzResearch.WordTrace]
  refine ⟨62888928733304237585791507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83851904977738983447722009 62888928733304237585791507)
  ·
    refine ⟨94333393099956356378687261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62888928733304237585791507 94333393099956356378687261)
    ·
      refine ⟨35375022412483633642007723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94333393099956356378687261 35375022412483633642007723)
      ·
        refine ⟨53062533618725450463011585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35375022412483633642007723 53062533618725450463011585)
        ·
          refine ⟨39796900214044087847258689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53062533618725450463011585 39796900214044087847258689)
          ·
            refine ⟨29847675160533065885444017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39796900214044087847258689 29847675160533065885444017)
            ·
              refine ⟨22385756370399799414083013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29847675160533065885444017 22385756370399799414083013)
              ·
                refine ⟨4197329319449962390140565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22385756370399799414083013 4197329319449962390140565)
                ·
                  refine ⟨196749811849216987037839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4197329319449962390140565 196749811849216987037839)
                  ·
                    rfl

theorem cell23_3448520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 4, 6].length) (baseStart_3448520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3448520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3448520 prefixEnd_3448520 := by exact prefixLift 3448520
  have htrace : WordTrace (prefixWord ++ tailWord_3448520) baseStart_3448520 baseEnd_3448520 := by
    simpa [prefixWord, tailWord_3448520, baseEnd_3448520] using wordTrace_append hprefix tailTrace_3448520
  have hstable : (prefixWord ++ tailWord_3448520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448520).length < 2 ^ (prefixWord ++ tailWord_3448520).sum := by decide
  have hdescent : baseEnd_3448520 < baseStart_3448520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448523 : List Nat := [1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 8]
def baseStart_3448523 : Nat := 118140960795 + 3448523 * 2 ^ 59
def prefixEnd_3448523 : Nat := 4983230072969 + 3 ^ 40 * 3448523 * 2
def baseEnd_3448523 : Nat := 1770749847084916371603037

theorem tailTrace_3448523 : CollatzResearch.WordTrace tailWord_3448523 prefixEnd_3448523 1770749847084916371603037 := by
  unfold tailWord_3448523
  simp only [CollatzResearch.WordTrace]
  refine ⟨125777966885597606683942223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83851977923731737789294815 125777966885597606683942223)
  ·
    refine ⟨188666950328396410025913335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125777966885597606683942223 188666950328396410025913335)
    ·
      refine ⟨283000425492594615038870003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188666950328396410025913335 283000425492594615038870003)
      ·
        refine ⟨424500638238891922558305005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283000425492594615038870003 424500638238891922558305005)
        ·
          refine ⟨159187739339584470959364377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 424500638238891922558305005 159187739339584470959364377)
          ·
            refine ⟨119390804504688353219523283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159187739339584470959364377 119390804504688353219523283)
            ·
              refine ⟨179086206757032529829284925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119390804504688353219523283 179086206757032529829284925)
              ·
                refine ⟨67157327533887198685981847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179086206757032529829284925 67157327533887198685981847)
                ·
                  refine ⟨100735991300830798028972771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67157327533887198685981847 100735991300830798028972771)
                  ·
                    refine ⟨151103986951246197043459157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 100735991300830798028972771 151103986951246197043459157)
                    ·
                      refine ⟨1770749847084916371603037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 151103986951246197043459157 1770749847084916371603037)
                      ·
                        rfl

theorem cell23_3448523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 8].length) (baseStart_3448523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3448523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3448523 prefixEnd_3448523 := by exact prefixLift 3448523
  have htrace : WordTrace (prefixWord ++ tailWord_3448523) baseStart_3448523 baseEnd_3448523 := by
    simpa [prefixWord, tailWord_3448523, baseEnd_3448523] using wordTrace_append hprefix tailTrace_3448523
  have hstable : (prefixWord ++ tailWord_3448523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448523).length < 2 ^ (prefixWord ++ tailWord_3448523).sum := by decide
  have hdescent : baseEnd_3448523 < baseStart_3448523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448537 : List Nat := [1, 2, 1, 2, 3, 3, 4, 1, 6]
def baseStart_3448537 : Nat := 118140960795 + 3448537 * 2 ^ 59
def prefixEnd_3448537 : Nat := 4983230072969 + 3 ^ 40 * 3448537 * 2
def baseEnd_3448537 : Nat := 196750781757119924091997

theorem tailTrace_3448537 : CollatzResearch.WordTrace tailWord_3448537 prefixEnd_3448537 196750781757119924091997 := by
  unfold tailWord_3448537
  simp only [CollatzResearch.WordTrace]
  refine ⟨125778477507546887074951865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83852318338364591383301243 125778477507546887074951865)
  ·
    refine ⟨94333858130660165306213899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125778477507546887074951865 94333858130660165306213899)
    ·
      refine ⟨141500787195990247959320849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94333858130660165306213899 141500787195990247959320849)
      ·
        refine ⟨106125590396992685969490637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141500787195990247959320849 106125590396992685969490637)
        ·
          refine ⟨39797096398872257238558989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106125590396992685969490637 39797096398872257238558989)
          ·
            refine ⟨14923911149577096464459621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39797096398872257238558989 14923911149577096464459621)
            ·
              refine ⟨2798233340545705587086179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14923911149577096464459621 2798233340545705587086179)
              ·
                refine ⟨4197350010818558380629269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2798233340545705587086179 4197350010818558380629269)
                ·
                  refine ⟨196750781757119924091997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4197350010818558380629269 196750781757119924091997)
                  ·
                    rfl

theorem cell23_3448537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 1, 6].length) (baseStart_3448537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3448537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3448537 prefixEnd_3448537 := by exact prefixLift 3448537
  have htrace : WordTrace (prefixWord ++ tailWord_3448537) baseStart_3448537 baseEnd_3448537 := by
    simpa [prefixWord, tailWord_3448537, baseEnd_3448537] using wordTrace_append hprefix tailTrace_3448537
  have hstable : (prefixWord ++ tailWord_3448537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448537).length < 2 ^ (prefixWord ++ tailWord_3448537).sum := by decide
  have hdescent : baseEnd_3448537 < baseStart_3448537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448551 : List Nat := [1, 1, 5, 4, 1, 1, 2, 1, 2, 2, 3]
def baseStart_3448551 : Nat := 118140960795 + 3448551 * 2 ^ 59
def prefixEnd_3448551 : Nat := 4983230072969 + 3 ^ 40 * 3448551 * 2
def baseEnd_3448551 : Nat := 1770764224543242262052909

theorem tailTrace_3448551 : CollatzResearch.WordTrace tailWord_3448551 prefixEnd_3448551 1770764224543242262052909 := by
  unfold tailWord_3448551
  simp only [CollatzResearch.WordTrace]
  refine ⟨125778988129496167465961507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83852658752997444977307671 125778988129496167465961507)
  ·
    refine ⟨188668482194244251198942261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125778988129496167465961507 188668482194244251198942261)
    ·
      refine ⟨17687670205710398549900837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 188668482194244251198942261 17687670205710398549900837)
      ·
        refine ⟨3316438163570699728106407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17687670205710398549900837 3316438163570699728106407)
        ·
          refine ⟨4974657245356049592159611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3316438163570699728106407 4974657245356049592159611)
          ·
            refine ⟨7461985868034074388239417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4974657245356049592159611 7461985868034074388239417)
            ·
              refine ⟨5596489401025555791179563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7461985868034074388239417 5596489401025555791179563)
              ·
                refine ⟨8394734101538333686769345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5596489401025555791179563 8394734101538333686769345)
                ·
                  refine ⟨6296050576153750265077009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8394734101538333686769345 6296050576153750265077009)
                  ·
                    refine ⟨4722037932115312698807757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6296050576153750265077009 4722037932115312698807757)
                    ·
                      refine ⟨1770764224543242262052909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4722037932115312698807757 1770764224543242262052909)
                      ·
                        rfl

theorem cell23_3448551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_3448551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3448551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3448551 prefixEnd_3448551 := by exact prefixLift 3448551
  have htrace : WordTrace (prefixWord ++ tailWord_3448551) baseStart_3448551 baseEnd_3448551 := by
    simpa [prefixWord, tailWord_3448551, baseEnd_3448551] using wordTrace_append hprefix tailTrace_3448551
  have hstable : (prefixWord ++ tailWord_3448551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448551).length < 2 ^ (prefixWord ++ tailWord_3448551).sum := by decide
  have hdescent : baseEnd_3448551 < baseStart_3448551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448582 : List Nat := [6, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2]
def baseStart_3448582 : Nat := 118140960795 + 3448582 * 2 ^ 59
def prefixEnd_3448582 : Nat := 4983230072969 + 3 ^ 40 * 3448582 * 2
def baseEnd_3448582 : Nat := 1770780142443531640765267

theorem tailTrace_3448582 : CollatzResearch.WordTrace tailWord_3448582 prefixEnd_3448582 1770780142443531640765267 := by
  unfold tailWord_3448582
  simp only [CollatzResearch.WordTrace]
  refine ⟨3930628712261995617510625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 83853412528255906506893333 3930628712261995617510625)
  ·
    refine ⟨2947971534196496713132969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3930628712261995617510625 2947971534196496713132969)
    ·
      refine ⟨2210978650647372534849727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2947971534196496713132969 2210978650647372534849727)
      ·
        refine ⟨3316467975971058802274591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2210978650647372534849727 3316467975971058802274591)
        ·
          refine ⟨4974701963956588203411887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3316467975971058802274591 4974701963956588203411887)
          ·
            refine ⟨7462052945934882305117831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4974701963956588203411887 7462052945934882305117831)
            ·
              refine ⟨11193079418902323457676747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7462052945934882305117831 11193079418902323457676747)
              ·
                refine ⟨16789619128353485186515121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11193079418902323457676747 16789619128353485186515121)
                ·
                  refine ⟨12592214346265113889886341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16789619128353485186515121 12592214346265113889886341)
                  ·
                    refine ⟨2361040189924708854353689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12592214346265113889886341 2361040189924708854353689)
                    ·
                      refine ⟨1770780142443531640765267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2361040189924708854353689 1770780142443531640765267)
                      ·
                        rfl

theorem cell23_3448582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_3448582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3448582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3448582 prefixEnd_3448582 := by exact prefixLift 3448582
  have htrace : WordTrace (prefixWord ++ tailWord_3448582) baseStart_3448582 baseEnd_3448582 := by
    simpa [prefixWord, tailWord_3448582, baseEnd_3448582] using wordTrace_append hprefix tailTrace_3448582
  have hstable : (prefixWord ++ tailWord_3448582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448582).length < 2 ^ (prefixWord ++ tailWord_3448582).sum := by decide
  have hdescent : baseEnd_3448582 < baseStart_3448582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448597 : List Nat := [1, 3, 2, 1, 2, 4, 2, 1, 1, 6]
def baseStart_3448597 : Nat := 118140960795 + 3448597 * 2 ^ 59
def prefixEnd_3448597 : Nat := 4983230072969 + 3 ^ 40 * 3448597 * 2
def baseEnd_3448597 : Nat := 590262614884449694025899

theorem tailTrace_3448597 : CollatzResearch.WordTrace tailWord_3448597 prefixEnd_3448597 590262614884449694025899 := by
  unfold tailWord_3448597
  simp only [CollatzResearch.WordTrace]
  refine ⟨125780665887329517322136045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83853777258219678214757363 125780665887329517322136045)
  ·
    refine ⟨47167749707748568995801017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125780665887329517322136045 47167749707748568995801017)
    ·
      refine ⟨35375812280811426746850763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47167749707748568995801017 35375812280811426746850763)
      ·
        refine ⟨53063718421217140120276145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35375812280811426746850763 53063718421217140120276145)
        ·
          refine ⟨39797788815912855090207109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53063718421217140120276145 39797788815912855090207109)
          ·
            refine ⟨7462085402983660329413833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39797788815912855090207109 7462085402983660329413833)
            ·
              refine ⟨5596564052237745247060375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7462085402983660329413833 5596564052237745247060375)
              ·
                refine ⟨8394846078356617870590563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5596564052237745247060375 8394846078356617870590563)
                ·
                  refine ⟨12592269117534926805885845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8394846078356617870590563 12592269117534926805885845)
                  ·
                    refine ⟨590262614884449694025899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12592269117534926805885845 590262614884449694025899)
                    ·
                      rfl

theorem cell23_3448597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 6].length) (baseStart_3448597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3448597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3448597 prefixEnd_3448597 := by exact prefixLift 3448597
  have htrace : WordTrace (prefixWord ++ tailWord_3448597) baseStart_3448597 baseEnd_3448597 := by
    simpa [prefixWord, tailWord_3448597, baseEnd_3448597] using wordTrace_append hprefix tailTrace_3448597
  have hstable : (prefixWord ++ tailWord_3448597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448597).length < 2 ^ (prefixWord ++ tailWord_3448597).sum := by decide
  have hdescent : baseEnd_3448597 < baseStart_3448597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448600 : List Nat := [2, 1, 2, 3, 1, 1, 2, 3, 1, 1, 6]
def baseStart_3448600 : Nat := 118140960795 + 3448600 * 2 ^ 59
def prefixEnd_3448600 : Nat := 4983230072969 + 3 ^ 40 * 3448600 * 2
def baseEnd_3448600 : Nat := 1770789385095312570340183

theorem tailTrace_3448600 : CollatzResearch.WordTrace tailWord_3448600 prefixEnd_3448600 1770789385095312570340183 := by
  unfold tailWord_3448600
  simp only [CollatzResearch.WordTrace]
  refine ⟨62890387653159324417247627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83853850204212432556330169 62890387653159324417247627)
  ·
    refine ⟨94335581479738986625871441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62890387653159324417247627 94335581479738986625871441)
    ·
      refine ⟨70751686109804239969403581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94335581479738986625871441 70751686109804239969403581)
      ·
        refine ⟨26531882291176589988526343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70751686109804239969403581 26531882291176589988526343)
        ·
          refine ⟨39797823436764884982789515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26531882291176589988526343 39797823436764884982789515)
          ·
            refine ⟨59696735155147327474184273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39797823436764884982789515 59696735155147327474184273)
            ·
              refine ⟨44772551366360495605638205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59696735155147327474184273 44772551366360495605638205)
              ·
                refine ⟨16789706762385185852114327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44772551366360495605638205 16789706762385185852114327)
                ·
                  refine ⟨25184560143577778778171491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16789706762385185852114327 25184560143577778778171491)
                  ·
                    refine ⟨37776840215366668167257237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25184560143577778778171491 37776840215366668167257237)
                    ·
                      refine ⟨1770789385095312570340183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37776840215366668167257237 1770789385095312570340183)
                      ·
                        rfl

theorem cell23_3448600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_3448600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3448600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3448600 prefixEnd_3448600 := by exact prefixLift 3448600
  have htrace : WordTrace (prefixWord ++ tailWord_3448600) baseStart_3448600 baseEnd_3448600 := by
    simpa [prefixWord, tailWord_3448600, baseEnd_3448600] using wordTrace_append hprefix tailTrace_3448600
  have hstable : (prefixWord ++ tailWord_3448600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448600).length < 2 ^ (prefixWord ++ tailWord_3448600).sum := by decide
  have hdescent : baseEnd_3448600 < baseStart_3448600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448607 : List Nat := [1, 1, 2, 4, 2, 1, 1, 3, 3, 2, 3]
def baseStart_3448607 : Nat := 118140960795 + 3448607 * 2 ^ 59
def prefixEnd_3448607 : Nat := 4983230072969 + 3 ^ 40 * 3448607 * 2
def baseEnd_3448607 : Nat := 1770792979459894042952651

theorem tailTrace_3448607 : CollatzResearch.WordTrace tailWord_3448607 prefixEnd_3448607 1770792979459894042952651 := by
  unfold tailWord_3448607
  simp only [CollatzResearch.WordTrace]
  refine ⟨125781030617293289030000075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83854020411528859353333383 125781030617293289030000075)
  ·
    refine ⟨188671545925939933545000113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125781030617293289030000075 188671545925939933545000113)
    ·
      refine ⟨141503659444454950158750085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188671545925939933545000113 141503659444454950158750085)
      ·
        refine ⟨26531936145835303154765641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141503659444454950158750085 26531936145835303154765641)
        ·
          refine ⟨19898952109376477366074231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26531936145835303154765641 19898952109376477366074231)
          ·
            refine ⟨29848428164064716049111347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19898952109376477366074231 29848428164064716049111347)
            ·
              refine ⟨44772642246097074073667021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29848428164064716049111347 44772642246097074073667021)
              ·
                refine ⟨16789740842286402777625133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44772642246097074073667021 16789740842286402777625133)
                ·
                  refine ⟨6296152815857401041609425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16789740842286402777625133 6296152815857401041609425)
                  ·
                    refine ⟨4722114611893050781207069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6296152815857401041609425 4722114611893050781207069)
                    ·
                      refine ⟨1770792979459894042952651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4722114611893050781207069 1770792979459894042952651)
                      ·
                        rfl

theorem cell23_3448607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_3448607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3448607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3448607 prefixEnd_3448607 := by exact prefixLift 3448607
  have htrace : WordTrace (prefixWord ++ tailWord_3448607) baseStart_3448607 baseEnd_3448607 := by
    simpa [prefixWord, tailWord_3448607, baseEnd_3448607] using wordTrace_append hprefix tailTrace_3448607
  have hstable : (prefixWord ++ tailWord_3448607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448607).length < 2 ^ (prefixWord ++ tailWord_3448607).sum := by decide
  have hdescent : baseEnd_3448607 < baseStart_3448607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448638 : List Nat := [4, 2, 1, 2, 2, 2, 2, 1, 3, 2, 2]
def baseStart_3448638 : Nat := 118140960795 + 3448638 * 2 ^ 59
def prefixEnd_3448638 : Nat := 4983230072969 + 3 ^ 40 * 3448638 * 2
def baseEnd_3448638 : Nat := 1770808897360183421665009

theorem tailTrace_3448638 : CollatzResearch.WordTrace tailWord_3448638 prefixEnd_3448638 1770808897360183421665009 := by
  unfold tailWord_3448638
  simp only [CollatzResearch.WordTrace]
  refine ⟨15722770160022622665547321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83854774186787320882919045 15722770160022622665547321)
  ·
    refine ⟨11792077620016966999160491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15722770160022622665547321 11792077620016966999160491)
    ·
      refine ⟨17688116430025450498740737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11792077620016966999160491 17688116430025450498740737)
      ·
        refine ⟨13266087322519087874055553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17688116430025450498740737 13266087322519087874055553)
        ·
          refine ⟨9949565491889315905541665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13266087322519087874055553 9949565491889315905541665)
          ·
            refine ⟨7462174118916986929156249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9949565491889315905541665 7462174118916986929156249)
            ·
              refine ⟨5596630589187740196867187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7462174118916986929156249 5596630589187740196867187)
              ·
                refine ⟨8394945883781610295300781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5596630589187740196867187 8394945883781610295300781)
                ·
                  refine ⟨3148104706418103860737793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8394945883781610295300781 3148104706418103860737793)
                  ·
                    refine ⟨2361078529813577895553345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3148104706418103860737793 2361078529813577895553345)
                    ·
                      refine ⟨1770808897360183421665009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2361078529813577895553345 1770808897360183421665009)
                      ·
                        rfl

theorem cell23_3448638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_3448638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3448638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3448638 prefixEnd_3448638 := by exact prefixLift 3448638
  have htrace : WordTrace (prefixWord ++ tailWord_3448638) baseStart_3448638 baseEnd_3448638 := by
    simpa [prefixWord, tailWord_3448638, baseEnd_3448638] using wordTrace_append hprefix tailTrace_3448638
  have hstable : (prefixWord ++ tailWord_3448638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448638).length < 2 ^ (prefixWord ++ tailWord_3448638).sum := by decide
  have hdescent : baseEnd_3448638 < baseStart_3448638 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448697 : List Nat := [1, 2, 1, 3, 2, 2, 2, 1, 2, 4, 3]
def baseStart_3448697 : Nat := 118140960795 + 3448697 * 2 ^ 59
def prefixEnd_3448697 : Nat := 4983230072969 + 3 ^ 40 * 3448697 * 2
def baseEnd_3448697 : Nat := 1770839192718798690827237

theorem tailTrace_3448697 : CollatzResearch.WordTrace tailWord_3448697 prefixEnd_3448697 1770839192718798690827237 := by
  unfold tailWord_3448697
  simp only [CollatzResearch.WordTrace]
  refine ⟨125784313186967234400776345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83856208791311489600517563 125784313186967234400776345)
  ·
    refine ⟨94338234890225425800582259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125784313186967234400776345 94338234890225425800582259)
    ·
      refine ⟨141507352335338138700873389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94338234890225425800582259 141507352335338138700873389)
      ·
        refine ⟨53065257125751802012827521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141507352335338138700873389 53065257125751802012827521)
        ·
          refine ⟨39798942844313851509620641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53065257125751802012827521 39798942844313851509620641)
          ·
            refine ⟨29849207133235388632215481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39798942844313851509620641 29849207133235388632215481)
            ·
              refine ⟨22386905349926541474161611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29849207133235388632215481 22386905349926541474161611)
              ·
                refine ⟨33580358024889812211242417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22386905349926541474161611 33580358024889812211242417)
                ·
                  refine ⟨25185268518667359158431813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33580358024889812211242417 25185268518667359158431813)
                  ·
                    refine ⟨4722237847250129842205965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25185268518667359158431813 4722237847250129842205965)
                    ·
                      refine ⟨1770839192718798690827237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4722237847250129842205965 1770839192718798690827237)
                      ·
                        rfl

theorem cell23_3448697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 4, 3].length) (baseStart_3448697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3448697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3448697 prefixEnd_3448697 := by exact prefixLift 3448697
  have htrace : WordTrace (prefixWord ++ tailWord_3448697) baseStart_3448697 baseEnd_3448697 := by
    simpa [prefixWord, tailWord_3448697, baseEnd_3448697] using wordTrace_append hprefix tailTrace_3448697
  have hstable : (prefixWord ++ tailWord_3448697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448697).length < 2 ^ (prefixWord ++ tailWord_3448697).sum := by decide
  have hdescent : baseEnd_3448697 < baseStart_3448697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448728 : List Nat := [2, 1, 2, 6, 1, 1, 1, 2, 1, 4, 2]
def baseStart_3448728 : Nat := 118140960795 + 3448728 * 2 ^ 59
def prefixEnd_3448728 : Nat := 4983230072969 + 3 ^ 40 * 3448728 * 2
def baseEnd_3448728 : Nat := 1770855110619088069539595

theorem tailTrace_3448728 : CollatzResearch.WordTrace tailWord_3448728 prefixEnd_3448728 1770855110619088069539595 := by
  unfold tailWord_3448728
  simp only [CollatzResearch.WordTrace]
  refine ⟨62892721924927463347577419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83856962566569951130103225 62892721924927463347577419)
  ·
    refine ⟨94339082887391195021366129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62892721924927463347577419 94339082887391195021366129)
    ·
      refine ⟨70754312165543396266024597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94339082887391195021366129 70754312165543396266024597)
      ·
        refine ⟨3316608382759846699969903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 70754312165543396266024597 3316608382759846699969903)
        ·
          refine ⟨4974912574139770049954855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3316608382759846699969903 4974912574139770049954855)
          ·
            refine ⟨7462368861209655074932283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4974912574139770049954855 7462368861209655074932283)
            ·
              refine ⟨11193553291814482612398425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7462368861209655074932283 11193553291814482612398425)
              ·
                refine ⟨8395164968860861959298819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11193553291814482612398425 8395164968860861959298819)
                ·
                  refine ⟨12592747453291292938948229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8395164968860861959298819 12592747453291292938948229)
                  ·
                    refine ⟨2361140147492117426052793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12592747453291292938948229 2361140147492117426052793)
                    ·
                      refine ⟨1770855110619088069539595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2361140147492117426052793 1770855110619088069539595)
                      ·
                        rfl

theorem cell23_3448728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_3448728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3448728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3448728 prefixEnd_3448728 := by exact prefixLift 3448728
  have htrace : WordTrace (prefixWord ++ tailWord_3448728) baseStart_3448728 baseEnd_3448728 := by
    simpa [prefixWord, tailWord_3448728, baseEnd_3448728] using wordTrace_append hprefix tailTrace_3448728
  have hstable : (prefixWord ++ tailWord_3448728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448728).length < 2 ^ (prefixWord ++ tailWord_3448728).sum := by decide
  have hdescent : baseEnd_3448728 < baseStart_3448728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448767 : List Nat := [1, 1, 2, 2, 2, 1, 4, 2, 1, 3, 4]
def baseStart_3448767 : Nat := 118140960795 + 3448767 * 2 ^ 59
def prefixEnd_3448767 : Nat := 4983230072969 + 3 ^ 40 * 3448767 * 2
def baseEnd_3448767 : Nat := 1770875136364613416951915

theorem tailTrace_3448767 : CollatzResearch.WordTrace tailWord_3448767 prefixEnd_3448767 1770875136364613416951915 := by
  unfold tailWord_3448767
  simp only [CollatzResearch.WordTrace]
  refine ⟨125786866296713636355824555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83857910864475757570549703 125786866296713636355824555)
  ·
    refine ⟨188680299445070454533736833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125786866296713636355824555 188680299445070454533736833)
    ·
      refine ⟨141510224583802840900302625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188680299445070454533736833 141510224583802840900302625)
      ·
        refine ⟨106132668437852130675226969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141510224583802840900302625 106132668437852130675226969)
        ·
          refine ⟨79599501328389098006420227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106132668437852130675226969 79599501328389098006420227)
          ·
            refine ⟨119399251992583647009630341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79599501328389098006420227 119399251992583647009630341)
            ·
              refine ⟨22387359748609433814305689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119399251992583647009630341 22387359748609433814305689)
              ·
                refine ⟨16790519811457075360729267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22387359748609433814305689 16790519811457075360729267)
                ·
                  refine ⟨25185779717185613041093901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16790519811457075360729267 25185779717185613041093901)
                  ·
                    refine ⟨9444667393944604890410213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25185779717185613041093901 9444667393944604890410213)
                    ·
                      refine ⟨1770875136364613416951915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9444667393944604890410213 1770875136364613416951915)
                      ·
                        rfl

theorem cell23_3448767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 3, 4].length) (baseStart_3448767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3448767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3448767 prefixEnd_3448767 := by exact prefixLift 3448767
  have htrace : WordTrace (prefixWord ++ tailWord_3448767) baseStart_3448767 baseEnd_3448767 := by
    simpa [prefixWord, tailWord_3448767, baseEnd_3448767] using wordTrace_append hprefix tailTrace_3448767
  have hstable : (prefixWord ++ tailWord_3448767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448767).length < 2 ^ (prefixWord ++ tailWord_3448767).sum := by decide
  have hdescent : baseEnd_3448767 < baseStart_3448767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448784 : List Nat := [2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 4]
def baseStart_3448784 : Nat := 118140960795 + 3448784 * 2 ^ 59
def prefixEnd_3448784 : Nat := 4983230072969 + 3 ^ 40 * 3448784 * 2
def baseEnd_3448784 : Nat := 1770883865535739850439337

theorem tailTrace_3448784 : CollatzResearch.WordTrace tailWord_3448784 prefixEnd_3448784 1770883865535739850439337 := by
  unfold tailWord_3448784
  simp only [CollatzResearch.WordTrace]
  refine ⟨62893743168826024129596703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83858324225101365506128937 62893743168826024129596703)
  ·
    refine ⟨94340614753239036194395055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62893743168826024129596703 94340614753239036194395055)
    ·
      refine ⟨141510922129858554291592583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94340614753239036194395055 141510922129858554291592583)
      ·
        refine ⟨212266383194787831437388875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141510922129858554291592583 212266383194787831437388875)
        ·
          refine ⟨318399574792181747156083313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212266383194787831437388875 318399574792181747156083313)
          ·
            refine ⟨238799681094136310367062485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318399574792181747156083313 238799681094136310367062485)
            ·
              refine ⟨5596867525643819774228027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 238799681094136310367062485 5596867525643819774228027)
              ·
                refine ⟨8395301288465729661342041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5596867525643819774228027 8395301288465729661342041)
                ·
                  refine ⟨6296475966349297246006531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8395301288465729661342041 6296475966349297246006531)
                  ·
                    refine ⟨9444713949523945869009797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6296475966349297246006531 9444713949523945869009797)
                    ·
                      refine ⟨1770883865535739850439337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9444713949523945869009797 1770883865535739850439337)
                      ·
                        rfl

theorem cell23_3448784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 4].length) (baseStart_3448784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3448784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3448784 prefixEnd_3448784 := by exact prefixLift 3448784
  have htrace : WordTrace (prefixWord ++ tailWord_3448784) baseStart_3448784 baseEnd_3448784 := by
    simpa [prefixWord, tailWord_3448784, baseEnd_3448784] using wordTrace_append hprefix tailTrace_3448784
  have hstable : (prefixWord ++ tailWord_3448784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448784).length < 2 ^ (prefixWord ++ tailWord_3448784).sum := by decide
  have hdescent : baseEnd_3448784 < baseStart_3448784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448796 : List Nat := [2, 2, 6, 1, 2, 1, 1, 2, 2, 2, 2]
def baseStart_3448796 : Nat := 118140960795 + 3448796 * 2 ^ 59
def prefixEnd_3448796 : Nat := 4983230072969 + 3 ^ 40 * 3448796 * 2
def baseEnd_3448796 : Nat := 1770890027303593803489283

theorem tailTrace_3448796 : CollatzResearch.WordTrace tailWord_3448796 prefixEnd_3448796 1770890027303593803489283 := by
  unfold tailWord_3448796
  simp only [CollatzResearch.WordTrace]
  refine ⟨62893962006804287154315121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83858616009072382872420161 62893962006804287154315121)
  ·
    refine ⟨47170471505103215365736341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62893962006804287154315121 47170471505103215365736341)
    ·
      refine ⟨2211115851801713220268891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 47170471505103215365736341 2211115851801713220268891)
      ·
        refine ⟨3316673777702569830403337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2211115851801713220268891 3316673777702569830403337)
        ·
          refine ⟨2487505333276927372802503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3316673777702569830403337 2487505333276927372802503)
          ·
            refine ⟨3731257999915391059203755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2487505333276927372802503 3731257999915391059203755)
            ·
              refine ⟨5596886999873086588805633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3731257999915391059203755 5596886999873086588805633)
              ·
                refine ⟨4197665249904814941604225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5596886999873086588805633 4197665249904814941604225)
                ·
                  refine ⟨3148248937428611206203169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4197665249904814941604225 3148248937428611206203169)
                  ·
                    refine ⟨2361186703071458404652377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3148248937428611206203169 2361186703071458404652377)
                    ·
                      refine ⟨1770890027303593803489283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2361186703071458404652377 1770890027303593803489283)
                      ·
                        rfl

theorem cell23_3448796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_3448796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3448796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3448796 prefixEnd_3448796 := by exact prefixLift 3448796
  have htrace : WordTrace (prefixWord ++ tailWord_3448796) baseStart_3448796 baseEnd_3448796 := by
    simpa [prefixWord, tailWord_3448796, baseEnd_3448796] using wordTrace_append hprefix tailTrace_3448796
  have hstable : (prefixWord ++ tailWord_3448796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448796).length < 2 ^ (prefixWord ++ tailWord_3448796).sum := by decide
  have hdescent : baseEnd_3448796 < baseStart_3448796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448804 : List Nat := [2, 3, 1, 1, 1, 1, 4, 1, 4, 2, 3]
def baseStart_3448804 : Nat := 118140960795 + 3448804 * 2 ^ 59
def prefixEnd_3448804 : Nat := 4983230072969 + 3 ^ 40 * 3448804 * 2
def baseEnd_3448804 : Nat := 1770894135148829772189245

theorem tailTrace_3448804 : CollatzResearch.WordTrace tailWord_3448804 prefixEnd_3448804 1770894135148829772189245 := by
  unfold tailWord_3448804
  simp only [CollatzResearch.WordTrace]
  refine ⟨62894107898789795837460733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83858810531719727783280977 62894107898789795837460733)
  ·
    refine ⟨23585290462046173439047775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62894107898789795837460733 23585290462046173439047775)
    ·
      refine ⟨35377935693069260158571663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23585290462046173439047775 35377935693069260158571663)
      ·
        refine ⟨53066903539603890237857495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35377935693069260158571663 53066903539603890237857495)
        ·
          refine ⟨79600355309405835356786243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53066903539603890237857495 79600355309405835356786243)
          ·
            refine ⟨119400532964108753035179365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79600355309405835356786243 119400532964108753035179365)
            ·
              refine ⟨22387599930770391194096131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119400532964108753035179365 22387599930770391194096131)
              ·
                refine ⟨33581399896155586791144197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22387599930770391194096131 33581399896155586791144197)
                ·
                  refine ⟨6296512480529172523339537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33581399896155586791144197 6296512480529172523339537)
                  ·
                    refine ⟨4722384360396879392504653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6296512480529172523339537 4722384360396879392504653)
                    ·
                      refine ⟨1770894135148829772189245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4722384360396879392504653 1770894135148829772189245)
                      ·
                        rfl

theorem cell23_3448804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 4, 2, 3].length) (baseStart_3448804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3448804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3448804 prefixEnd_3448804 := by exact prefixLift 3448804
  have htrace : WordTrace (prefixWord ++ tailWord_3448804) baseStart_3448804 baseEnd_3448804 := by
    simpa [prefixWord, tailWord_3448804, baseEnd_3448804] using wordTrace_append hprefix tailTrace_3448804
  have hstable : (prefixWord ++ tailWord_3448804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448804).length < 2 ^ (prefixWord ++ tailWord_3448804).sum := by decide
  have hdescent : baseEnd_3448804 < baseStart_3448804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448888 : List Nat := [2, 1, 2, 1, 6, 2, 1, 2, 1, 5]
def baseStart_3448888 : Nat := 118140960795 + 3448888 * 2 ^ 59
def prefixEnd_3448888 : Nat := 4983230072969 + 3 ^ 40 * 3448888 * 2
def baseEnd_3448888 : Nat := 590312422507935814512953

theorem tailTrace_3448888 : CollatzResearch.WordTrace tailWord_3448888 prefixEnd_3448888 590312422507935814512953 := by
  unfold tailWord_3448888
  simp only [CollatzResearch.WordTrace]
  refine ⟨62895639764637637010489659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83860853019516849347319545 62895639764637637010489659)
  ·
    refine ⟨94343459646956455515734489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62895639764637637010489659 94343459646956455515734489)
    ·
      refine ⟨70757594735217341636800867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94343459646956455515734489 70757594735217341636800867)
      ·
        refine ⟨106136392102826012455201301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70757594735217341636800867 106136392102826012455201301)
        ·
          refine ⟨4975143379819969333837561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 106136392102826012455201301 4975143379819969333837561)
          ·
            refine ⟨3731357534864977000378171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4975143379819969333837561 3731357534864977000378171)
            ·
              refine ⟨5597036302297465500567257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3731357534864977000378171 5597036302297465500567257)
              ·
                refine ⟨4197777226723099125425443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5597036302297465500567257 4197777226723099125425443)
                ·
                  refine ⟨6296665840084648688138165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4197777226723099125425443 6296665840084648688138165)
                  ·
                    refine ⟨590312422507935814512953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6296665840084648688138165 590312422507935814512953)
                    ·
                      rfl

theorem cell23_3448888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 2, 1, 5].length) (baseStart_3448888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3448888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3448888 prefixEnd_3448888 := by exact prefixLift 3448888
  have htrace : WordTrace (prefixWord ++ tailWord_3448888) baseStart_3448888 baseEnd_3448888 := by
    simpa [prefixWord, tailWord_3448888, baseEnd_3448888] using wordTrace_append hprefix tailTrace_3448888
  have hstable : (prefixWord ++ tailWord_3448888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448888).length < 2 ^ (prefixWord ++ tailWord_3448888).sum := by decide
  have hdescent : baseEnd_3448888 < baseStart_3448888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448902 : List Nat := [6, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3]
def baseStart_3448902 : Nat := 118140960795 + 3448902 * 2 ^ 59
def prefixEnd_3448902 : Nat := 4983230072969 + 3 ^ 40 * 3448902 * 2
def baseEnd_3448902 : Nat := 1770944456252970388763795

theorem tailTrace_3448902 : CollatzResearch.WordTrace tailWord_3448902 prefixEnd_3448902 1770944456252970388763795 := by
  unfold tailWord_3448902
  simp only [CollatzResearch.WordTrace]
  refine ⟨3930993442225767325374655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 83861193434149702941325973 3930993442225767325374655)
  ·
    refine ⟨5896490163338650988061983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3930993442225767325374655 5896490163338650988061983)
    ·
      refine ⟨8844735245007976482092975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5896490163338650988061983 8844735245007976482092975)
      ·
        refine ⟨13267102867511964723139463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8844735245007976482092975 13267102867511964723139463)
        ·
          refine ⟨19900654301267947084709195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13267102867511964723139463 19900654301267947084709195)
          ·
            refine ⟨29850981451901920627063793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19900654301267947084709195 29850981451901920627063793)
            ·
              refine ⟨22388236088926440470297845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29850981451901920627063793 22388236088926440470297845)
              ·
                refine ⟨2098897133336853794090423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22388236088926440470297845 2098897133336853794090423)
                ·
                  refine ⟨3148345700005280691135635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2098897133336853794090423 3148345700005280691135635)
                  ·
                    refine ⟨4722518550007921036703453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3148345700005280691135635 4722518550007921036703453)
                    ·
                      refine ⟨1770944456252970388763795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4722518550007921036703453 1770944456252970388763795)
                      ·
                        rfl

theorem cell23_3448902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_3448902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3448902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3448902 prefixEnd_3448902 := by exact prefixLift 3448902
  have htrace : WordTrace (prefixWord ++ tailWord_3448902) baseStart_3448902 baseEnd_3448902 := by
    simpa [prefixWord, tailWord_3448902, baseEnd_3448902] using wordTrace_append hprefix tailTrace_3448902
  have hstable : (prefixWord ++ tailWord_3448902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448902).length < 2 ^ (prefixWord ++ tailWord_3448902).sum := by decide
  have hdescent : baseEnd_3448902 < baseStart_3448902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448914 : List Nat := [3, 2, 2, 1, 4, 11]
def baseStart_3448914 : Nat := 118140960795 + 3448914 * 2 ^ 59
def prefixEnd_3448914 : Nat := 4983230072969 + 3 ^ 40 * 3448914 * 2
def baseEnd_3448914 : Nat := 7287862625600100172073

theorem tailTrace_3448914 : CollatzResearch.WordTrace tailWord_3448914 prefixEnd_3448914 7287862625600100172073 := by
  unfold tailWord_3448914
  simp only [CollatzResearch.WordTrace]
  refine ⟨31448056956795270115356449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83861485218120720307617197 31448056956795270115356449)
  ·
    refine ⟨23586042717596452586517337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31448056956795270115356449 23586042717596452586517337)
    ·
      refine ⟨17689532038197339439888003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23586042717596452586517337 17689532038197339439888003)
      ·
        refine ⟨26534298057296009159832005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17689532038197339439888003 26534298057296009159832005)
        ·
          refine ⟨4975180885743001717468501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26534298057296009159832005 4975180885743001717468501)
          ·
            refine ⟨7287862625600100172073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4975180885743001717468501 7287862625600100172073)
            ·
              rfl

theorem cell23_3448914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 11].length) (baseStart_3448914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3448914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3448914 prefixEnd_3448914 := by exact prefixLift 3448914
  have htrace : WordTrace (prefixWord ++ tailWord_3448914) baseStart_3448914 baseEnd_3448914 := by
    simpa [prefixWord, tailWord_3448914, baseEnd_3448914] using wordTrace_append hprefix tailTrace_3448914
  have hstable : (prefixWord ++ tailWord_3448914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448914).length < 2 ^ (prefixWord ++ tailWord_3448914).sum := by decide
  have hdescent : baseEnd_3448914 < baseStart_3448914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448938 : List Nat := [3, 1, 3, 2, 3, 1, 2, 1, 1, 2, 4]
def baseStart_3448938 : Nat := 118140960795 + 3448938 * 2 ^ 59
def prefixEnd_3448938 : Nat := 4983230072969 + 3 ^ 40 * 3448938 * 2
def baseEnd_3448938 : Nat := 1770962941556532247913629

theorem tailTrace_3448938 : CollatzResearch.WordTrace tailWord_3448938 prefixEnd_3448938 1770962941556532247913629 := by
  unfold tailWord_3448938
  simp only [CollatzResearch.WordTrace]
  refine ⟨31448275794773533140074867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83862068786062755040199645 31448275794773533140074867)
  ·
    refine ⟨47172413692160299710112301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31448275794773533140074867 47172413692160299710112301)
    ·
      refine ⟨17689655134560112391292113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47172413692160299710112301 17689655134560112391292113)
      ·
        refine ⟨13267241350920084293469085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17689655134560112391292113 13267241350920084293469085)
        ·
          refine ⟨4975215506595031610050907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13267241350920084293469085 4975215506595031610050907)
          ·
            refine ⟨7462823259892547415076361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4975215506595031610050907 7462823259892547415076361)
            ·
              refine ⟨5597117444919410561307271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7462823259892547415076361 5597117444919410561307271)
              ·
                refine ⟨8395676167379115841960907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5597117444919410561307271 8395676167379115841960907)
                ·
                  refine ⟨12593514251068673762941361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8395676167379115841960907 12593514251068673762941361)
                  ·
                    refine ⟨9445135688301505322206021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12593514251068673762941361 9445135688301505322206021)
                    ·
                      refine ⟨1770962941556532247913629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9445135688301505322206021 1770962941556532247913629)
                      ·
                        rfl

theorem cell23_3448938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_3448938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3448938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3448938 prefixEnd_3448938 := by exact prefixLift 3448938
  have htrace : WordTrace (prefixWord ++ tailWord_3448938) baseStart_3448938 baseEnd_3448938 := by
    simpa [prefixWord, tailWord_3448938, baseEnd_3448938] using wordTrace_append hprefix tailTrace_3448938
  have hstable : (prefixWord ++ tailWord_3448938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448938).length < 2 ^ (prefixWord ++ tailWord_3448938).sum := by decide
  have hdescent : baseEnd_3448938 < baseStart_3448938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3448991 : List Nat := [1, 1, 2, 6, 1, 1, 2, 1, 2, 6]
def baseStart_3448991 : Nat := 118140960795 + 3448991 * 2 ^ 59
def prefixEnd_3448991 : Nat := 4983230072969 + 3 ^ 40 * 3448991 * 2
def baseEnd_3448991 : Nat := 590330052010406846850295

theorem tailTrace_3448991 : CollatzResearch.WordTrace tailWord_3448991 prefixEnd_3448991 590330052010406846850295 := by
  unfold tailWord_3448991
  simp only [CollatzResearch.WordTrace]
  refine ⟨125795036247902122611978827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83863357498601415074652551 125795036247902122611978827)
  ·
    refine ⟨188692554371853183917968241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125795036247902122611978827 188692554371853183917968241)
    ·
      refine ⟨141519415778889887938476181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188692554371853183917968241 141519415778889887938476181)
      ·
        refine ⟨6633722614635463497116071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 141519415778889887938476181 6633722614635463497116071)
        ·
          refine ⟨9950583921953195245674107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6633722614635463497116071 9950583921953195245674107)
          ·
            refine ⟨14925875882929792868511161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9950583921953195245674107 14925875882929792868511161)
            ·
              refine ⟨11194406912197344651383371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14925875882929792868511161 11194406912197344651383371)
              ·
                refine ⟨16791610368296016977075057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11194406912197344651383371 16791610368296016977075057)
                ·
                  refine ⟨12593707776222012732806293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16791610368296016977075057 12593707776222012732806293)
                  ·
                    refine ⟨590330052010406846850295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12593707776222012732806293 590330052010406846850295)
                    ·
                      rfl

theorem cell23_3448991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 6].length) (baseStart_3448991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3448991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3448991 prefixEnd_3448991 := by exact prefixLift 3448991
  have htrace : WordTrace (prefixWord ++ tailWord_3448991) baseStart_3448991 baseEnd_3448991 := by
    simpa [prefixWord, tailWord_3448991, baseEnd_3448991] using wordTrace_append hprefix tailTrace_3448991
  have hstable : (prefixWord ++ tailWord_3448991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3448991).length < 2 ^ (prefixWord ++ tailWord_3448991).sum := by decide
  have hdescent : baseEnd_3448991 < baseStart_3448991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3448991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449038 : List Nat := [4, 1, 1, 1, 4, 3, 1, 1, 7]
def baseStart_3449038 : Nat := 118140960795 + 3449038 * 2 ^ 59
def prefixEnd_3449038 : Nat := 4983230072969 + 3 ^ 40 * 3449038 * 2
def baseEnd_3449038 : Nat := 196779365513553539629241

theorem tailTrace_3449038 : CollatzResearch.WordTrace tailWord_3449038 prefixEnd_3449038 196779365513553539629241 := by
  unfold tailWord_3449038
  simp only [CollatzResearch.WordTrace]
  refine ⟨15724593809841481204867471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83864500319154566425959845 15724593809841481204867471)
  ·
    refine ⟨23586890714762221807301207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15724593809841481204867471 23586890714762221807301207)
    ·
      refine ⟨35380336072143332710951811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23586890714762221807301207 35380336072143332710951811)
      ·
        refine ⟨53070504108214999066427717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35380336072143332710951811 53070504108214999066427717)
        ·
          refine ⟨9950719520290312324955197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53070504108214999066427717 9950719520290312324955197)
          ·
            refine ⟨3731519820108867121858199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9950719520290312324955197 3731519820108867121858199)
            ·
              refine ⟨5597279730163300682787299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3731519820108867121858199 5597279730163300682787299)
              ·
                refine ⟨8395919595244951024180949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5597279730163300682787299 8395919595244951024180949)
                ·
                  refine ⟨196779365513553539629241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8395919595244951024180949 196779365513553539629241)
                  ·
                    rfl

theorem cell23_3449038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 7].length) (baseStart_3449038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3449038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3449038 prefixEnd_3449038 := by exact prefixLift 3449038
  have htrace : WordTrace (prefixWord ++ tailWord_3449038) baseStart_3449038 baseEnd_3449038 := by
    simpa [prefixWord, tailWord_3449038, baseEnd_3449038] using wordTrace_append hprefix tailTrace_3449038
  have hstable : (prefixWord ++ tailWord_3449038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449038).length < 2 ^ (prefixWord ++ tailWord_3449038).sum := by decide
  have hdescent : baseEnd_3449038 < baseStart_3449038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449081 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 7, 4]
def baseStart_3449081 : Nat := 118140960795 + 3449081 * 2 ^ 59
def prefixEnd_3449081 : Nat := 4983230072969 + 3 ^ 40 * 3449081 * 2
def baseEnd_3449081 : Nat := 590345456430041729475157

theorem tailTrace_3449081 : CollatzResearch.WordTrace tailWord_3449081 prefixEnd_3449081 590345456430041729475157 := by
  unfold tailWord_3449081
  simp only [CollatzResearch.WordTrace]
  refine ⟨125798318817576067982755097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83865545878384045321836731 125798318817576067982755097)
  ·
    refine ⟨94348739113182050987066323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125798318817576067982755097 94348739113182050987066323)
    ·
      refine ⟨141523108669773076480599485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94348739113182050987066323 141523108669773076480599485)
      ·
        refine ⟨53071165751164903680224807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141523108669773076480599485 53071165751164903680224807)
        ·
          refine ⟨79606748626747355520337211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53071165751164903680224807 79606748626747355520337211)
          ·
            refine ⟨119410122940121033280505817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79606748626747355520337211 119410122940121033280505817)
            ·
              refine ⟨89557592205090774960379363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119410122940121033280505817 89557592205090774960379363)
              ·
                refine ⟨134336388307636162440569045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89557592205090774960379363 134336388307636162440569045)
                ·
                  refine ⟨3148509100960222557200837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 134336388307636162440569045 3148509100960222557200837)
                  ·
                    refine ⟨590345456430041729475157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3148509100960222557200837 590345456430041729475157)
                    ·
                      rfl

theorem cell23_3449081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 7, 4].length) (baseStart_3449081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3449081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3449081 prefixEnd_3449081 := by exact prefixLift 3449081
  have htrace : WordTrace (prefixWord ++ tailWord_3449081) baseStart_3449081 baseEnd_3449081 := by
    simpa [prefixWord, tailWord_3449081, baseEnd_3449081] using wordTrace_append hprefix tailTrace_3449081
  have hstable : (prefixWord ++ tailWord_3449081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449081).length < 2 ^ (prefixWord ++ tailWord_3449081).sum := by decide
  have hdescent : baseEnd_3449081 < baseStart_3449081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449145 : List Nat := [1, 2, 1, 6, 1, 3, 1, 2, 6]
def baseStart_3449145 : Nat := 118140960795 + 3449145 * 2 ^ 59
def prefixEnd_3449145 : Nat := 4983230072969 + 3 ^ 40 * 3449145 * 2
def baseEnd_3449145 : Nat := 196785470228001437558353

theorem tailTrace_3449145 : CollatzResearch.WordTrace tailWord_3449145 prefixEnd_3449145 196785470228001437558353 := by
  unfold tailWord_3449145
  simp only [CollatzResearch.WordTrace]
  refine ⟨125800653089344206913084889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83867102059562804608723259 125800653089344206913084889)
  ·
    refine ⟨94350489817008155184813667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125800653089344206913084889 94350489817008155184813667)
    ·
      refine ⟨141525734725512232777220501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94350489817008155184813667 141525734725512232777220501)
      ·
        refine ⟨6634018815258385911432211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 141525734725512232777220501 6634018815258385911432211)
        ·
          refine ⟨9951028222887578867148317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6634018815258385911432211 9951028222887578867148317)
          ·
            refine ⟨3731635583582842075180619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9951028222887578867148317 3731635583582842075180619)
            ·
              refine ⟨5597453375374263112770929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3731635583582842075180619 5597453375374263112770929)
              ·
                refine ⟨4198090031530697334578197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5597453375374263112770929 4198090031530697334578197)
                ·
                  refine ⟨196785470228001437558353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4198090031530697334578197 196785470228001437558353)
                  ·
                    rfl

theorem cell23_3449145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 2, 6].length) (baseStart_3449145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3449145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3449145 prefixEnd_3449145 := by exact prefixLift 3449145
  have htrace : WordTrace (prefixWord ++ tailWord_3449145) baseStart_3449145 baseEnd_3449145 := by
    simpa [prefixWord, tailWord_3449145, baseEnd_3449145] using wordTrace_append hprefix tailTrace_3449145
  have hstable : (prefixWord ++ tailWord_3449145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449145).length < 2 ^ (prefixWord ++ tailWord_3449145).sum := by decide
  have hdescent : baseEnd_3449145 < baseStart_3449145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449171 : List Nat := [1, 1, 1, 2, 1, 1, 4, 5, 1, 6]
def baseStart_3449171 : Nat := 118140960795 + 3449171 * 2 ^ 59
def prefixEnd_3449171 : Nat := 4983230072969 + 3 ^ 40 * 3449171 * 2
def baseEnd_3449171 : Nat := 590360860849676612100019

theorem tailTrace_3449171 : CollatzResearch.WordTrace tailWord_3449171 prefixEnd_3449171 590360860849676612100019 := by
  unfold tailWord_3449171
  simp only [CollatzResearch.WordTrace]
  refine ⟨125801601387250013353531367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83867734258166675569020911 125801601387250013353531367)
  ·
    refine ⟨188702402080875020030297051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125801601387250013353531367 188702402080875020030297051)
    ·
      refine ⟨283053603121312530045445577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188702402080875020030297051 283053603121312530045445577)
      ·
        refine ⟨212290202340984397534084183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283053603121312530045445577 212290202340984397534084183)
        ·
          refine ⟨318435303511476596301126275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212290202340984397534084183 318435303511476596301126275)
          ·
            refine ⟨477652955267214894451689413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318435303511476596301126275 477652955267214894451689413)
            ·
              refine ⟨89559929112602792709691765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 477652955267214894451689413 89559929112602792709691765)
              ·
                refine ⟨8396243354306511816533603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89559929112602792709691765 8396243354306511816533603)
                ·
                  refine ⟨12594365031459767724800405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8396243354306511816533603 12594365031459767724800405)
                  ·
                    refine ⟨590360860849676612100019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12594365031459767724800405 590360860849676612100019)
                    ·
                      rfl

theorem cell23_3449171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 6].length) (baseStart_3449171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3449171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3449171 prefixEnd_3449171 := by exact prefixLift 3449171
  have htrace : WordTrace (prefixWord ++ tailWord_3449171) baseStart_3449171 baseEnd_3449171 := by
    simpa [prefixWord, tailWord_3449171, baseEnd_3449171] using wordTrace_append hprefix tailTrace_3449171
  have hstable : (prefixWord ++ tailWord_3449171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449171).length < 2 ^ (prefixWord ++ tailWord_3449171).sum := by decide
  have hdescent : baseEnd_3449171 < baseStart_3449171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449178 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 1, 8, 2]
def baseStart_3449178 : Nat := 118140960795 + 3449178 * 2 ^ 59
def prefixEnd_3449178 : Nat := 4983230072969 + 3 ^ 40 * 3449178 * 2
def baseEnd_3449178 : Nat := 1771086176913611308912525

theorem tailTrace_3449178 : CollatzResearch.WordTrace tailWord_3449178 prefixEnd_3449178 1771086176913611308912525 := by
  unfold tailWord_3449178
  simp only [CollatzResearch.WordTrace]
  refine ⟨31450464174556163387259047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83867904465483102366024125 31450464174556163387259047)
  ·
    refine ⟨47175696261834245080888571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31450464174556163387259047 47175696261834245080888571)
    ·
      refine ⟨70763544392751367621332857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47175696261834245080888571 70763544392751367621332857)
      ·
        refine ⟨53072658294563525715999643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70763544392751367621332857 53072658294563525715999643)
        ·
          refine ⟨79608987441845288573999465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53072658294563525715999643 79608987441845288573999465)
          ·
            refine ⟨59706740581383966430499599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79608987441845288573999465 59706740581383966430499599)
            ·
              refine ⟨89560110872075949645749399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59706740581383966430499599 89560110872075949645749399)
              ·
                refine ⟨134340166308113924468624099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89560110872075949645749399 134340166308113924468624099)
                ·
                  refine ⟨201510249462170886702936149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134340166308113924468624099 201510249462170886702936149)
                  ·
                    refine ⟨2361448235884815078550033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 201510249462170886702936149 2361448235884815078550033)
                    ·
                      refine ⟨1771086176913611308912525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2361448235884815078550033 1771086176913611308912525)
                      ·
                        rfl

theorem cell23_3449178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 1, 8, 2].length) (baseStart_3449178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3449178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3449178 prefixEnd_3449178 := by exact prefixLift 3449178
  have htrace : WordTrace (prefixWord ++ tailWord_3449178) baseStart_3449178 baseEnd_3449178 := by
    simpa [prefixWord, tailWord_3449178, baseEnd_3449178] using wordTrace_append hprefix tailTrace_3449178
  have hstable : (prefixWord ++ tailWord_3449178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449178).length < 2 ^ (prefixWord ++ tailWord_3449178).sum := by decide
  have hdescent : baseEnd_3449178 < baseStart_3449178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449188 : List Nat := [2, 3, 1, 1, 3, 1, 1, 1, 6, 4]
def baseStart_3449188 : Nat := 118140960795 + 3449188 * 2 ^ 59
def prefixEnd_3449188 : Nat := 4983230072969 + 3 ^ 40 * 3449188 * 2
def baseEnd_3449188 : Nat := 590363770573385423262493

theorem tailTrace_3449188 : CollatzResearch.WordTrace tailWord_3449188 prefixEnd_3449188 590363770573385423262493 := by
  unfold tailWord_3449188
  simp only [CollatzResearch.WordTrace]
  refine ⟨62901110714094212628450109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83868147618792283504600145 62901110714094212628450109)
  ·
    refine ⟨23587916517785329735668791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62901110714094212628450109 23587916517785329735668791)
    ·
      refine ⟨35381874776677994603503187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23587916517785329735668791 35381874776677994603503187)
      ·
        refine ⟨53072812165016991905254781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35381874776677994603503187 53072812165016991905254781)
        ·
          refine ⟨19902304561881371964470543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53072812165016991905254781 19902304561881371964470543)
          ·
            refine ⟨29853456842822057946705815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19902304561881371964470543 29853456842822057946705815)
            ·
              refine ⟨44780185264233086920058723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29853456842822057946705815 44780185264233086920058723)
              ·
                refine ⟨67170277896349630380088085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44780185264233086920058723 67170277896349630380088085)
                ·
                  refine ⟨3148606776391388924066629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 67170277896349630380088085 3148606776391388924066629)
                  ·
                    refine ⟨590363770573385423262493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3148606776391388924066629 590363770573385423262493)
                    ·
                      rfl

theorem cell23_3449188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 6, 4].length) (baseStart_3449188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3449188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3449188 prefixEnd_3449188 := by exact prefixLift 3449188
  have htrace : WordTrace (prefixWord ++ tailWord_3449188) baseStart_3449188 baseEnd_3449188 := by
    simpa [prefixWord, tailWord_3449188, baseEnd_3449188] using wordTrace_append hprefix tailTrace_3449188
  have hstable : (prefixWord ++ tailWord_3449188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449188).length < 2 ^ (prefixWord ++ tailWord_3449188).sum := by decide
  have hdescent : baseEnd_3449188 < baseStart_3449188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449189 : List Nat := [1, 3, 1, 3, 1, 5, 1, 3, 1, 1, 3]
def baseStart_3449189 : Nat := 118140960795 + 3449189 * 2 ^ 59
def prefixEnd_3449189 : Nat := 4983230072969 + 3 ^ 40 * 3449189 * 2
def baseEnd_3449189 : Nat := 1771091825200810765874975

theorem tailTrace_3449189 : CollatzResearch.WordTrace tailWord_3449189 prefixEnd_3449189 1771091825200810765874975 := by
  unfold tailWord_3449189
  simp only [CollatzResearch.WordTrace]
  refine ⟨125802257901184802427686621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83868171934123201618457747 125802257901184802427686621)
  ·
    refine ⟨47175846712944300910382483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125802257901184802427686621 47175846712944300910382483)
    ·
      refine ⟨70763770069416451365573725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47175846712944300910382483 70763770069416451365573725)
      ·
        refine ⟨26536413776031169262090147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70763770069416451365573725 26536413776031169262090147)
        ·
          refine ⟨39804620664046753893135221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26536413776031169262090147 39804620664046753893135221)
          ·
            refine ⟨3731683187254383177481427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39804620664046753893135221 3731683187254383177481427)
            ·
              refine ⟨5597524780881574766222141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3731683187254383177481427 5597524780881574766222141)
              ·
                refine ⟨2099071792830590537333303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5597524780881574766222141 2099071792830590537333303)
                ·
                  refine ⟨3148607689245885805999955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2099071792830590537333303 3148607689245885805999955)
                  ·
                    refine ⟨4722911533868828708999933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3148607689245885805999955 4722911533868828708999933)
                    ·
                      refine ⟨1771091825200810765874975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4722911533868828708999933 1771091825200810765874975)
                      ·
                        rfl

theorem cell23_3449189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 3, 1, 1, 3].length) (baseStart_3449189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3449189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3449189 prefixEnd_3449189 := by exact prefixLift 3449189
  have htrace : WordTrace (prefixWord ++ tailWord_3449189) baseStart_3449189 baseEnd_3449189 := by
    simpa [prefixWord, tailWord_3449189, baseEnd_3449189] using wordTrace_append hprefix tailTrace_3449189
  have hstable : (prefixWord ++ tailWord_3449189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449189).length < 2 ^ (prefixWord ++ tailWord_3449189).sum := by decide
  have hdescent : baseEnd_3449189 < baseStart_3449189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449205 : List Nat := [1, 3, 4, 1, 2, 1, 2, 1, 4, 4]
def baseStart_3449205 : Nat := 118140960795 + 3449205 * 2 ^ 59
def prefixEnd_3449205 : Nat := 4983230072969 + 3 ^ 40 * 3449205 * 2
def baseEnd_3449205 : Nat := 590366680297094234424967

theorem tailTrace_3449205 : CollatzResearch.WordTrace tailWord_3449205 prefixEnd_3449205 590366680297094234424967 := by
  unfold tailWord_3449205
  simp only [CollatzResearch.WordTrace]
  refine ⟨125802841469126837160269069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83868560979417891440179379 125802841469126837160269069)
  ·
    refine ⟨47176065550922563935100901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125802841469126837160269069 47176065550922563935100901)
    ·
      refine ⟨8845512290797980737831419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47176065550922563935100901 8845512290797980737831419)
      ·
        refine ⟨13268268436196971106747129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8845512290797980737831419 13268268436196971106747129)
        ·
          refine ⟨9951201327147728330060347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13268268436196971106747129 9951201327147728330060347)
          ·
            refine ⟨14926801990721592495090521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9951201327147728330060347 14926801990721592495090521)
            ·
              refine ⟨11195101493041194371317891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14926801990721592495090521 11195101493041194371317891)
              ·
                refine ⟨16792652239561791556976837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11195101493041194371317891 16792652239561791556976837)
                ·
                  refine ⟨3148622294917835916933157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16792652239561791556976837 3148622294917835916933157)
                  ·
                    refine ⟨590366680297094234424967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3148622294917835916933157 590366680297094234424967)
                    ·
                      rfl

theorem cell23_3449205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_3449205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3449205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3449205 prefixEnd_3449205 := by exact prefixLift 3449205
  have htrace : WordTrace (prefixWord ++ tailWord_3449205) baseStart_3449205 baseEnd_3449205 := by
    simpa [prefixWord, tailWord_3449205, baseEnd_3449205] using wordTrace_append hprefix tailTrace_3449205
  have hstable : (prefixWord ++ tailWord_3449205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449205).length < 2 ^ (prefixWord ++ tailWord_3449205).sum := by decide
  have hdescent : baseEnd_3449205 < baseStart_3449205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449206 : List Nat := [5, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3]
def baseStart_3449206 : Nat := 118140960795 + 3449206 * 2 ^ 59
def prefixEnd_3449206 : Nat := 4983230072969 + 3 ^ 40 * 3449206 * 2
def baseEnd_3449206 : Nat := 1771100554371937199362397

theorem tailTrace_3449206 : CollatzResearch.WordTrace tailWord_3449206 prefixEnd_3449206 1771100554371937199362397 := by
  unfold tailWord_3449206
  simp only [CollatzResearch.WordTrace]
  refine ⟨7862679871382700895690967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83868585294748809554036981 7862679871382700895690967)
  ·
    refine ⟨11794019807074051343536451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7862679871382700895690967 11794019807074051343536451)
    ·
      refine ⟨17691029710611077015304677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11794019807074051343536451 17691029710611077015304677)
      ·
        refine ⟨3317068070739576940369627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17691029710611077015304677 3317068070739576940369627)
        ·
          refine ⟨4975602106109365410554441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3317068070739576940369627 4975602106109365410554441)
          ·
            refine ⟨3731701579582024057915831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4975602106109365410554441 3731701579582024057915831)
            ·
              refine ⟨5597552369373036086873747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3731701579582024057915831 5597552369373036086873747)
              ·
                refine ⟨8396328554059554130310621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5597552369373036086873747 8396328554059554130310621)
                ·
                  refine ⟨3148623207772332798866483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8396328554059554130310621 3148623207772332798866483)
                  ·
                    refine ⟨4722934811658499198299725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3148623207772332798866483 4722934811658499198299725)
                    ·
                      refine ⟨1771100554371937199362397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4722934811658499198299725 1771100554371937199362397)
                      ·
                        rfl

theorem cell23_3449206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_3449206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3449206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3449206 prefixEnd_3449206 := by exact prefixLift 3449206
  have htrace : WordTrace (prefixWord ++ tailWord_3449206) baseStart_3449206 baseEnd_3449206 := by
    simpa [prefixWord, tailWord_3449206, baseEnd_3449206] using wordTrace_append hprefix tailTrace_3449206
  have hstable : (prefixWord ++ tailWord_3449206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449206).length < 2 ^ (prefixWord ++ tailWord_3449206).sum := by decide
  have hdescent : baseEnd_3449206 < baseStart_3449206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449221 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 1, 4, 6]
def baseStart_3449221 : Nat := 118140960795 + 3449221 * 2 ^ 59
def prefixEnd_3449221 : Nat := 4983230072969 + 3 ^ 40 * 3449221 * 2
def baseEnd_3449221 : Nat := 1771108256581754640674827

theorem tailTrace_3449221 : CollatzResearch.WordTrace tailWord_3449221 prefixEnd_3449221 1771108256581754640674827 := by
  unfold tailWord_3449221
  simp only [CollatzResearch.WordTrace]
  refine ⟨125803425037068871892851517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83868950024712581261901011 125803425037068871892851517)
  ·
    refine ⟨47176284388900826959819319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125803425037068871892851517 47176284388900826959819319)
    ·
      refine ⟨70764426583351240439728979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47176284388900826959819319 70764426583351240439728979)
      ·
        refine ⟨106146639875026860659593469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70764426583351240439728979 106146639875026860659593469)
        ·
          refine ⟨39804989953135072747347551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106146639875026860659593469 39804989953135072747347551)
          ·
            refine ⟨59707484929702609121021327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39804989953135072747347551 59707484929702609121021327)
            ·
              refine ⟨89561227394553913681531991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59707484929702609121021327 89561227394553913681531991)
              ·
                refine ⟨134341841091830870522297987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89561227394553913681531991 134341841091830870522297987)
                ·
                  refine ⟨201512761637746305783446981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134341841091830870522297987 201512761637746305783446981)
                  ·
                    refine ⟨37783642807077432334396309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 201512761637746305783446981 37783642807077432334396309)
                    ·
                      refine ⟨1771108256581754640674827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37783642807077432334396309 1771108256581754640674827)
                      ·
                        rfl

theorem cell23_3449221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 4, 6].length) (baseStart_3449221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3449221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3449221 prefixEnd_3449221 := by exact prefixLift 3449221
  have htrace : WordTrace (prefixWord ++ tailWord_3449221) baseStart_3449221 baseEnd_3449221 := by
    simpa [prefixWord, tailWord_3449221, baseEnd_3449221] using wordTrace_append hprefix tailTrace_3449221
  have hstable : (prefixWord ++ tailWord_3449221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449221).length < 2 ^ (prefixWord ++ tailWord_3449221).sum := by decide
  have hdescent : baseEnd_3449221 < baseStart_3449221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449249 : List Nat := [1, 2, 3, 5, 2, 1, 1, 1, 1, 1, 5]
def baseStart_3449249 : Nat := 118140960795 + 3449249 * 2 ^ 59
def prefixEnd_3449249 : Nat := 4983230072969 + 3 ^ 40 * 3449249 * 2
def baseEnd_3449249 : Nat := 1771122634040080531124699

theorem tailTrace_3449249 : CollatzResearch.WordTrace tailWord_3449249 prefixEnd_3449249 1771122634040080531124699 := by
  unfold tailWord_3449249
  simp only [CollatzResearch.WordTrace]
  refine ⟨125804446280967432674870801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83869630853978288449913867 125804446280967432674870801)
  ·
    refine ⟨94353334710725574506153101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125804446280967432674870801 94353334710725574506153101)
    ·
      refine ⟨35382500516522090439807413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94353334710725574506153101 35382500516522090439807413)
      ·
        refine ⟨3317109423423945978731945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35382500516522090439807413 3317109423423945978731945)
        ·
          refine ⟨2487832067567959484048959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3317109423423945978731945 2487832067567959484048959)
          ·
            refine ⟨3731748101351939226073439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2487832067567959484048959 3731748101351939226073439)
            ·
              refine ⟨5597622152027908839110159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3731748101351939226073439 5597622152027908839110159)
              ·
                refine ⟨8396433228041863258665239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5597622152027908839110159 8396433228041863258665239)
                ·
                  refine ⟨12594649842062794887997859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8396433228041863258665239 12594649842062794887997859)
                  ·
                    refine ⟨18891974763094192331996789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12594649842062794887997859 18891974763094192331996789)
                    ·
                      refine ⟨1771122634040080531124699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18891974763094192331996789 1771122634040080531124699)
                      ·
                        rfl

theorem cell23_3449249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_3449249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3449249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3449249 prefixEnd_3449249 := by exact prefixLift 3449249
  have htrace : WordTrace (prefixWord ++ tailWord_3449249) baseStart_3449249 baseEnd_3449249 := by
    simpa [prefixWord, tailWord_3449249, baseEnd_3449249] using wordTrace_append hprefix tailTrace_3449249
  have hstable : (prefixWord ++ tailWord_3449249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449249).length < 2 ^ (prefixWord ++ tailWord_3449249).sum := by decide
  have hdescent : baseEnd_3449249 < baseStart_3449249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449278 : List Nat := [4, 2, 1, 1, 1, 1, 3, 1, 1, 8]
def baseStart_3449278 : Nat := 118140960795 + 3449278 * 2 ^ 59
def prefixEnd_3449278 : Nat := 4983230072969 + 3 ^ 40 * 3449278 * 2
def baseEnd_3449278 : Nat := 590379174993020305887355

theorem tailTrace_3449278 : CollatzResearch.WordTrace tailWord_3449278 prefixEnd_3449278 590379174993020305887355 := by
  unfold tailWord_3449278
  simp only [CollatzResearch.WordTrace]
  refine ⟨15725687999732796328459561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83870335998574913751784325 15725687999732796328459561)
  ·
    refine ⟨11794265999799597246344671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15725687999732796328459561 11794265999799597246344671)
    ·
      refine ⟨17691398999699395869517007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11794265999799597246344671 17691398999699395869517007)
      ·
        refine ⟨26537098499549093804275511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17691398999699395869517007 26537098499549093804275511)
        ·
          refine ⟨39805647749323640706413267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26537098499549093804275511 39805647749323640706413267)
          ·
            refine ⟨59708471623985461059619901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39805647749323640706413267 59708471623985461059619901)
            ·
              refine ⟨22390676858994547897357463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59708471623985461059619901 22390676858994547897357463)
              ·
                refine ⟨33586015288491821846036195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22390676858994547897357463 33586015288491821846036195)
                ·
                  refine ⟨50379022932737732769054293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33586015288491821846036195 50379022932737732769054293)
                  ·
                    refine ⟨590379174993020305887355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 50379022932737732769054293 590379174993020305887355)
                    ·
                      rfl

theorem cell23_3449278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_3449278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3449278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3449278 prefixEnd_3449278 := by exact prefixLift 3449278
  have htrace : WordTrace (prefixWord ++ tailWord_3449278) baseStart_3449278 baseEnd_3449278 := by
    simpa [prefixWord, tailWord_3449278, baseEnd_3449278] using wordTrace_append hprefix tailTrace_3449278
  have hstable : (prefixWord ++ tailWord_3449278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449278).length < 2 ^ (prefixWord ++ tailWord_3449278).sum := by decide
  have hdescent : baseEnd_3449278 < baseStart_3449278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449325 : List Nat := [1, 5, 1, 3, 1, 1, 1, 3, 7]
def baseStart_3449325 : Nat := 118140960795 + 3449325 * 2 ^ 59
def prefixEnd_3449325 : Nat := 4983230072969 + 3 ^ 40 * 3449325 * 2
def baseEnd_3449325 : Nat := 196795739841091359308261

theorem tailTrace_3449325 : CollatzResearch.WordTrace tailWord_3449325 prefixEnd_3449325 196795739841091359308261 := by
  unfold tailWord_3449325
  simp only [CollatzResearch.WordTrace]
  refine ⟨125807218228692097654637429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83871478819128065103091619 125807218228692097654637429)
  ·
    refine ⟨11794426708939884155122259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125807218228692097654637429 11794426708939884155122259)
    ·
      refine ⟨17691640063409826232683389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11794426708939884155122259 17691640063409826232683389)
      ·
        refine ⟨6634365023778684837256271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17691640063409826232683389 6634365023778684837256271)
        ·
          refine ⟨9951547535668027255884407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6634365023778684837256271 9951547535668027255884407)
          ·
            refine ⟨14927321303502040883826611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9951547535668027255884407 14927321303502040883826611)
            ·
              refine ⟨22390981955253061325739917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14927321303502040883826611 22390981955253061325739917)
              ·
                refine ⟨8396618233219897997152469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22390981955253061325739917 8396618233219897997152469)
                ·
                  refine ⟨196795739841091359308261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8396618233219897997152469 196795739841091359308261)
                  ·
                    rfl

theorem cell23_3449325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 7].length) (baseStart_3449325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3449325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3449325 prefixEnd_3449325 := by exact prefixLift 3449325
  have htrace : WordTrace (prefixWord ++ tailWord_3449325) baseStart_3449325 baseEnd_3449325 := by
    simpa [prefixWord, tailWord_3449325, baseEnd_3449325] using wordTrace_append hprefix tailTrace_3449325
  have hstable : (prefixWord ++ tailWord_3449325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449325).length < 2 ^ (prefixWord ++ tailWord_3449325).sum := by decide
  have hdescent : baseEnd_3449325 < baseStart_3449325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449338 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 6, 5]
def baseStart_3449338 : Nat := 118140960795 + 3449338 * 2 ^ 59
def prefixEnd_3449338 : Nat := 4983230072969 + 3 ^ 40 * 3449338 * 2
def baseEnd_3449338 : Nat := 590389444606110227637263

theorem tailTrace_3449338 : CollatzResearch.WordTrace tailWord_3449338 prefixEnd_3449338 590389444606110227637263 := by
  unfold tailWord_3449338
  simp only [CollatzResearch.WordTrace]
  refine ⟨31451923094411250218715167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83871794918430000583240445 31451923094411250218715167)
  ·
    refine ⟨47177884641616875328072751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31451923094411250218715167 47177884641616875328072751)
    ·
      refine ⟨70766826962425312992109127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47177884641616875328072751 70766826962425312992109127)
      ·
        refine ⟨106150240443637969488163691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70766826962425312992109127 106150240443637969488163691)
        ·
          refine ⟨159225360665456954232245537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106150240443637969488163691 159225360665456954232245537)
          ·
            refine ⟨119419020499092715674184153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159225360665456954232245537 119419020499092715674184153)
            ·
              refine ⟨89564265374319536755638115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119419020499092715674184153 89564265374319536755638115)
              ·
                refine ⟨134346398061479305133457173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89564265374319536755638115 134346398061479305133457173)
                ·
                  refine ⟨6297487409131842428130805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 134346398061479305133457173 6297487409131842428130805)
                  ·
                    refine ⟨590389444606110227637263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6297487409131842428130805 590389444606110227637263)
                    ·
                      rfl

theorem cell23_3449338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 6, 5].length) (baseStart_3449338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3449338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3449338 prefixEnd_3449338 := by exact prefixLift 3449338
  have htrace : WordTrace (prefixWord ++ tailWord_3449338) baseStart_3449338 baseEnd_3449338 := by
    simpa [prefixWord, tailWord_3449338, baseEnd_3449338] using wordTrace_append hprefix tailTrace_3449338
  have hstable : (prefixWord ++ tailWord_3449338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449338).length < 2 ^ (prefixWord ++ tailWord_3449338).sum := by decide
  have hdescent : baseEnd_3449338 < baseStart_3449338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449388 : List Nat := [2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 6]
def baseStart_3449388 : Nat := 118140960795 + 3449388 * 2 ^ 59
def prefixEnd_3449388 : Nat := 4983230072969 + 3 ^ 40 * 3449388 * 2
def baseEnd_3449388 : Nat := 1771194007851055487286559

theorem tailTrace_3449388 : CollatzResearch.WordTrace tailWord_3449388 prefixEnd_3449388 1771194007851055487286559 := by
  unfold tailWord_3449388
  simp only [CollatzResearch.WordTrace]
  refine ⟨62904758013731929707090409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83873010684975906276120545 62904758013731929707090409)
  ·
    refine ⟨47178568510298947280317807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62904758013731929707090409 47178568510298947280317807)
    ·
      refine ⟨70767852765448420920476711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47178568510298947280317807 70767852765448420920476711)
      ·
        refine ⟨106151779148172631380715067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70767852765448420920476711 106151779148172631380715067)
        ·
          refine ⟨159227668722258947071072601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106151779148172631380715067 159227668722258947071072601)
          ·
            refine ⟨119420751541694210303304451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159227668722258947071072601 119420751541694210303304451)
            ·
              refine ⟨179131127312541315454956677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119420751541694210303304451 179131127312541315454956677)
              ·
                refine ⟨33587086371101496647804377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 179131127312541315454956677 33587086371101496647804377)
                ·
                  refine ⟨25190314778326122485853283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33587086371101496647804377 25190314778326122485853283)
                  ·
                    refine ⟨37785472167489183728779925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25190314778326122485853283 37785472167489183728779925)
                    ·
                      refine ⟨1771194007851055487286559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37785472167489183728779925 1771194007851055487286559)
                      ·
                        rfl

theorem cell23_3449388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 6].length) (baseStart_3449388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3449388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3449388 prefixEnd_3449388 := by exact prefixLift 3449388
  have htrace : WordTrace (prefixWord ++ tailWord_3449388) baseStart_3449388 baseEnd_3449388 := by
    simpa [prefixWord, tailWord_3449388, baseEnd_3449388] using wordTrace_append hprefix tailTrace_3449388
  have hstable : (prefixWord ++ tailWord_3449388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449388).length < 2 ^ (prefixWord ++ tailWord_3449388).sum := by decide
  have hdescent : baseEnd_3449388 < baseStart_3449388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449395 : List Nat := [1, 1, 1, 2, 4, 2, 1, 2, 4, 2, 3]
def baseStart_3449395 : Nat := 118140960795 + 3449395 * 2 ^ 59
def prefixEnd_3449395 : Nat := 4983230072969 + 3 ^ 40 * 3449395 * 2
def baseEnd_3449395 : Nat := 1771197602215636959899027

theorem tailTrace_3449395 : CollatzResearch.WordTrace tailWord_3449395 prefixEnd_3449395 1771197602215636959899027 := by
  unfold tailWord_3449395
  simp only [CollatzResearch.WordTrace]
  refine ⟨125809771338438499609685639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83873180892292333073123759 125809771338438499609685639)
  ·
    refine ⟨188714657007657749414528459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125809771338438499609685639 188714657007657749414528459)
    ·
      refine ⟨283071985511486624121792689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188714657007657749414528459 283071985511486624121792689)
      ·
        refine ⟨212303989133614968091344517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283071985511486624121792689 212303989133614968091344517)
        ·
          refine ⟨39806997962552806517127097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212303989133614968091344517 39806997962552806517127097)
          ·
            refine ⟨29855248471914604887845323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39806997962552806517127097 29855248471914604887845323)
            ·
              refine ⟨44782872707871907331767985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29855248471914604887845323 44782872707871907331767985)
              ·
                refine ⟨33587154530903930498825989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44782872707871907331767985 33587154530903930498825989)
                ·
                  refine ⟨6297591474544486968529873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33587154530903930498825989 6297591474544486968529873)
                  ·
                    refine ⟨4723193605908365226397405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6297591474544486968529873 4723193605908365226397405)
                    ·
                      refine ⟨1771197602215636959899027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4723193605908365226397405 1771197602215636959899027)
                      ·
                        rfl

theorem cell23_3449395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 4, 2, 3].length) (baseStart_3449395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3449395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3449395 prefixEnd_3449395 := by exact prefixLift 3449395
  have htrace : WordTrace (prefixWord ++ tailWord_3449395) baseStart_3449395 baseEnd_3449395 := by
    simpa [prefixWord, tailWord_3449395, baseEnd_3449395] using wordTrace_append hprefix tailTrace_3449395
  have hstable : (prefixWord ++ tailWord_3449395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449395).length < 2 ^ (prefixWord ++ tailWord_3449395).sum := by decide
  have hdescent : baseEnd_3449395 < baseStart_3449395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449436 : List Nat := [2, 2, 4, 1, 3, 1, 1, 4, 1, 4]
def baseStart_3449436 : Nat := 118140960795 + 3449436 * 2 ^ 59
def prefixEnd_3449436 : Nat := 4983230072969 + 3 ^ 40 * 3449436 * 2
def baseEnd_3449436 : Nat := 590406218307490433162113

theorem tailTrace_3449436 : CollatzResearch.WordTrace tailWord_3449436 prefixEnd_3449436 590406218307490433162113 := by
  unfold tailWord_3449436
  simp only [CollatzResearch.WordTrace]
  refine ⟨62905633365644981805964081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83874177820859975741285441 62905633365644981805964081)
  ·
    refine ⟨47179225024233736354473061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62905633365644981805964081 47179225024233736354473061)
    ·
      refine ⟨8846104692043825566463699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47179225024233736354473061 8846104692043825566463699)
      ·
        refine ⟨13269157038065738349695549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8846104692043825566463699 13269157038065738349695549)
        ·
          refine ⟨4975933889274651881135831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13269157038065738349695549 4975933889274651881135831)
          ·
            refine ⟨7463900833911977821703747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4975933889274651881135831 7463900833911977821703747)
            ·
              refine ⟨11195851250867966732555621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7463900833911977821703747 11195851250867966732555621)
              ·
                refine ⟨2099222109537743762354179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11195851250867966732555621 2099222109537743762354179)
                ·
                  refine ⟨3148833164306615643531269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2099222109537743762354179 3148833164306615643531269)
                  ·
                    refine ⟨590406218307490433162113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3148833164306615643531269 590406218307490433162113)
                    ·
                      rfl

theorem cell23_3449436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_3449436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3449436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3449436 prefixEnd_3449436 := by exact prefixLift 3449436
  have htrace : WordTrace (prefixWord ++ tailWord_3449436) baseStart_3449436 baseEnd_3449436 := by
    simpa [prefixWord, tailWord_3449436, baseEnd_3449436] using wordTrace_append hprefix tailTrace_3449436
  have hstable : (prefixWord ++ tailWord_3449436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449436).length < 2 ^ (prefixWord ++ tailWord_3449436).sum := by decide
  have hdescent : baseEnd_3449436 < baseStart_3449436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449452 : List Nat := [2, 2, 1, 1, 3, 1, 2, 2, 4, 3, 2]
def baseStart_3449452 : Nat := 118140960795 + 3449452 * 2 ^ 59
def prefixEnd_3449452 : Nat := 4983230072969 + 3 ^ 40 * 3449452 * 2
def baseEnd_3449452 : Nat := 1771226870612943236886265

theorem tailTrace_3449452 : CollatzResearch.WordTrace tailWord_3449452 prefixEnd_3449452 1771226870612943236886265 := by
  unfold tailWord_3449452
  simp only [CollatzResearch.WordTrace]
  refine ⟨62905925149615999172255305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83874566866154665563007073 62905925149615999172255305)
  ·
    refine ⟨47179443862211999379191479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62905925149615999172255305 47179443862211999379191479)
    ·
      refine ⟨70769165793317999068787219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47179443862211999379191479 70769165793317999068787219)
      ·
        refine ⟨106153748689976998603180829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70769165793317999068787219 106153748689976998603180829)
        ·
          refine ⟨39807655758741374476192811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106153748689976998603180829 39807655758741374476192811)
          ·
            refine ⟨59711483638112061714289217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39807655758741374476192811 59711483638112061714289217)
            ·
              refine ⟨44783612728584046285716913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59711483638112061714289217 44783612728584046285716913)
              ·
                refine ⟨33587709546438034714287685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44783612728584046285716913 33587709546438034714287685)
                ·
                  refine ⟨6297695539957131508928941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33587709546438034714287685 6297695539957131508928941)
                  ·
                    refine ⟨2361635827483924315848353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6297695539957131508928941 2361635827483924315848353)
                    ·
                      refine ⟨1771226870612943236886265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2361635827483924315848353 1771226870612943236886265)
                      ·
                        rfl

theorem cell23_3449452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 3, 2].length) (baseStart_3449452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3449452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3449452 prefixEnd_3449452 := by exact prefixLift 3449452
  have htrace : WordTrace (prefixWord ++ tailWord_3449452) baseStart_3449452 baseEnd_3449452 := by
    simpa [prefixWord, tailWord_3449452, baseEnd_3449452] using wordTrace_append hprefix tailTrace_3449452
  have hstable : (prefixWord ++ tailWord_3449452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449452).length < 2 ^ (prefixWord ++ tailWord_3449452).sum := by decide
  have hdescent : baseEnd_3449452 < baseStart_3449452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449469 : List Nat := [1, 4, 1, 1, 5, 1, 1, 1, 1, 5, 2]
def baseStart_3449469 : Nat := 118140960795 + 3449469 * 2 ^ 59
def prefixEnd_3449469 : Nat := 4983230072969 + 3 ^ 40 * 3449469 * 2
def baseEnd_3449469 : Nat := 1771235599784069670373687

theorem tailTrace_3449469 : CollatzResearch.WordTrace tailWord_3449469 prefixEnd_3449469 1771235599784069670373687 := by
  unfold tailWord_3449469
  simp only [CollatzResearch.WordTrace]
  refine ⟨125812470340170410247879461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83874980226780273498586307 125812470340170410247879461)
  ·
    refine ⟨23589838188781951921477399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125812470340170410247879461 23589838188781951921477399)
    ·
      refine ⟨35384757283172927882216099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23589838188781951921477399 35384757283172927882216099)
      ·
        refine ⟨53077135924759391823324149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35384757283172927882216099 53077135924759391823324149)
        ·
          refine ⟨4975981492946192983436639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53077135924759391823324149 4975981492946192983436639)
          ·
            refine ⟨7463972239419289475154959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4975981492946192983436639 7463972239419289475154959)
            ·
              refine ⟨11195958359128934212732439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7463972239419289475154959 11195958359128934212732439)
              ·
                refine ⟨16793937538693401319098659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11195958359128934212732439 16793937538693401319098659)
                ·
                  refine ⟨25190906308040101978647989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16793937538693401319098659 25190906308040101978647989)
                  ·
                    refine ⟨2361647466378759560498249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25190906308040101978647989 2361647466378759560498249)
                    ·
                      refine ⟨1771235599784069670373687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2361647466378759560498249 1771235599784069670373687)
                      ·
                        rfl

theorem cell23_3449469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 5, 2].length) (baseStart_3449469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3449469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3449469 prefixEnd_3449469 := by exact prefixLift 3449469
  have htrace : WordTrace (prefixWord ++ tailWord_3449469) baseStart_3449469 baseEnd_3449469 := by
    simpa [prefixWord, tailWord_3449469, baseEnd_3449469] using wordTrace_append hprefix tailTrace_3449469
  have hstable : (prefixWord ++ tailWord_3449469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449469).length < 2 ^ (prefixWord ++ tailWord_3449469).sum := by decide
  have hdescent : baseEnd_3449469 < baseStart_3449469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449475 : List Nat := [1, 1, 1, 3, 3, 1, 4, 2, 1, 6]
def baseStart_3449475 : Nat := 118140960795 + 3449475 * 2 ^ 59
def prefixEnd_3449475 : Nat := 4983230072969 + 3 ^ 40 * 3449475 * 2
def baseEnd_3449475 : Nat := 590412893555998882299553

theorem tailTrace_3449475 : CollatzResearch.WordTrace tailWord_3449475 prefixEnd_3449475 590412893555998882299553 := by
  unfold tailWord_3449475
  simp only [CollatzResearch.WordTrace]
  refine ⟨125812689178148673272597879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83875126118765782181731919 125812689178148673272597879)
  ·
    refine ⟨188719033767223009908896819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125812689178148673272597879 188719033767223009908896819)
    ·
      refine ⟨283078550650834514863345229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188719033767223009908896819 283078550650834514863345229)
      ·
        refine ⟨106154456494062943073754461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 283078550650834514863345229 106154456494062943073754461)
        ·
          refine ⟨39807921185273603652657923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106154456494062943073754461 39807921185273603652657923)
          ·
            refine ⟨59711881777910405478986885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39807921185273603652657923 59711881777910405478986885)
            ·
              refine ⟨11195977833358201027310041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59711881777910405478986885 11195977833358201027310041)
              ·
                refine ⟨8396983375018650770482531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11195977833358201027310041 8396983375018650770482531)
                ·
                  refine ⟨12595475062527976155723797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8396983375018650770482531 12595475062527976155723797)
                  ·
                    refine ⟨590412893555998882299553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12595475062527976155723797 590412893555998882299553)
                    ·
                      rfl

theorem cell23_3449475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 6].length) (baseStart_3449475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3449475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3449475 prefixEnd_3449475 := by exact prefixLift 3449475
  have htrace : WordTrace (prefixWord ++ tailWord_3449475) baseStart_3449475 baseEnd_3449475 := by
    simpa [prefixWord, tailWord_3449475, baseEnd_3449475] using wordTrace_append hprefix tailTrace_3449475
  have hstable : (prefixWord ++ tailWord_3449475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449475).length < 2 ^ (prefixWord ++ tailWord_3449475).sum := by decide
  have hdescent : baseEnd_3449475 < baseStart_3449475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449476 : List Nat := [2, 3, 2, 1, 3, 1, 1, 5, 1, 1, 3]
def baseStart_3449476 : Nat := 118140960795 + 3449476 * 2 ^ 59
def prefixEnd_3449476 : Nat := 4983230072969 + 3 ^ 40 * 3449476 * 2
def baseEnd_3449476 : Nat := 1771239194148651142986155

theorem tailTrace_3449476 : CollatzResearch.WordTrace tailWord_3449476 prefixEnd_3449476 1771239194148651142986155 := by
  unfold tailWord_3449476
  simp only [CollatzResearch.WordTrace]
  refine ⟨62906362825572525221692141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83875150434096700295589521 62906362825572525221692141)
  ·
    refine ⟨23589886059589696958134553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62906362825572525221692141 23589886059589696958134553)
    ·
      refine ⟨17692414544692272718600915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23589886059589696958134553 17692414544692272718600915)
      ·
        refine ⟨26538621817038409077901373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17692414544692272718600915 26538621817038409077901373)
        ·
          refine ⟨9951983181389403404213015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26538621817038409077901373 9951983181389403404213015)
          ·
            refine ⟨14927974772084105106319523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9951983181389403404213015 14927974772084105106319523)
            ·
              refine ⟨22391962158126157659479285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14927974772084105106319523 22391962158126157659479285)
              ·
                refine ⟨2099246452324327280576183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22391962158126157659479285 2099246452324327280576183)
                ·
                  refine ⟨3148869678486490920864275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2099246452324327280576183 3148869678486490920864275)
                  ·
                    refine ⟨4723304517729736381296413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3148869678486490920864275 4723304517729736381296413)
                    ·
                      refine ⟨1771239194148651142986155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4723304517729736381296413 1771239194148651142986155)
                      ·
                        rfl

theorem cell23_3449476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 5, 1, 1, 3].length) (baseStart_3449476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3449476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3449476 prefixEnd_3449476 := by exact prefixLift 3449476
  have htrace : WordTrace (prefixWord ++ tailWord_3449476) baseStart_3449476 baseEnd_3449476 := by
    simpa [prefixWord, tailWord_3449476, baseEnd_3449476] using wordTrace_append hprefix tailTrace_3449476
  have hstable : (prefixWord ++ tailWord_3449476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449476).length < 2 ^ (prefixWord ++ tailWord_3449476).sum := by decide
  have hdescent : baseEnd_3449476 < baseStart_3449476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449495 : List Nat := [1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 6]
def baseStart_3449495 : Nat := 118140960795 + 3449495 * 2 ^ 59
def prefixEnd_3449495 : Nat := 4983230072969 + 3 ^ 40 * 3449495 * 2
def baseEnd_3449495 : Nat := 1771248950281086568648567

theorem tailTrace_3449495 : CollatzResearch.WordTrace tailWord_3449495 prefixEnd_3449495 1771248950281086568648567 := by
  unfold tailWord_3449495
  simp only [CollatzResearch.WordTrace]
  refine ⟨125813418638076216688325939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83875612425384144458883959 125813418638076216688325939)
  ·
    refine ⟨188720127957114325032488909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125813418638076216688325939 188720127957114325032488909)
    ·
      refine ⟨70770047983917871887183341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188720127957114325032488909 70770047983917871887183341)
      ·
        refine ⟨26538767993969201957693753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70770047983917871887183341 26538767993969201957693753)
        ·
          refine ⟨19904075995476901468270315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26538767993969201957693753 19904075995476901468270315)
          ·
            refine ⟨29856113993215352202405473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19904075995476901468270315 29856113993215352202405473)
            ·
              refine ⟨22392085494911514151804105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29856113993215352202405473 22392085494911514151804105)
              ·
                refine ⟨16794064121183635613853079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22392085494911514151804105 16794064121183635613853079)
                ·
                  refine ⟨25191096181775453420779619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16794064121183635613853079 25191096181775453420779619)
                  ·
                    refine ⟨37786644272663180131169429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25191096181775453420779619 37786644272663180131169429)
                    ·
                      refine ⟨1771248950281086568648567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37786644272663180131169429 1771248950281086568648567)
                      ·
                        rfl

theorem cell23_3449495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_3449495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3449495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3449495 prefixEnd_3449495 := by exact prefixLift 3449495
  have htrace : WordTrace (prefixWord ++ tailWord_3449495) baseStart_3449495 baseEnd_3449495 := by
    simpa [prefixWord, tailWord_3449495, baseEnd_3449495] using wordTrace_append hprefix tailTrace_3449495
  have hstable : (prefixWord ++ tailWord_3449495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449495).length < 2 ^ (prefixWord ++ tailWord_3449495).sum := by decide
  have hdescent : baseEnd_3449495 < baseStart_3449495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449519 : List Nat := [1, 1, 2, 1, 2, 6, 2, 2, 1, 2, 3]
def baseStart_3449519 : Nat := 118140960795 + 3449519 * 2 ^ 59
def prefixEnd_3449519 : Nat := 4983230072969 + 3 ^ 40 * 3449519 * 2
def baseEnd_3449519 : Nat := 1771261273816794474748457

theorem tailTrace_3449519 : CollatzResearch.WordTrace tailWord_3449519 prefixEnd_3449519 1771261273816794474748457 := by
  unfold tailWord_3449519
  simp only [CollatzResearch.WordTrace]
  refine ⟨125814293989989268787199611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83876195993326179191466407 125814293989989268787199611)
  ·
    refine ⟨188721440984983903180799417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125814293989989268787199611 188721440984983903180799417)
    ·
      refine ⟨141541080738737927385599563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188721440984983903180799417 141541080738737927385599563)
      ·
        refine ⟨212311621108106891078399345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141541080738737927385599563 212311621108106891078399345)
        ·
          refine ⟨159233715831080168308799509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212311621108106891078399345 159233715831080168308799509)
          ·
            refine ⟨7464080429581882889474977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 159233715831080168308799509 7464080429581882889474977)
            ·
              refine ⟨5598060322186412167106233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7464080429581882889474977 5598060322186412167106233)
              ·
                refine ⟨4198545241639809125329675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5598060322186412167106233 4198545241639809125329675)
                ·
                  refine ⟨6297817862459713687994513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4198545241639809125329675 6297817862459713687994513)
                  ·
                    refine ⟨4723363396844785265995885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6297817862459713687994513 4723363396844785265995885)
                    ·
                      refine ⟨1771261273816794474748457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4723363396844785265995885 1771261273816794474748457)
                      ·
                        rfl

theorem cell23_3449519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 2, 1, 2, 3].length) (baseStart_3449519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3449519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3449519 prefixEnd_3449519 := by exact prefixLift 3449519
  have htrace : WordTrace (prefixWord ++ tailWord_3449519) baseStart_3449519 baseEnd_3449519 := by
    simpa [prefixWord, tailWord_3449519, baseEnd_3449519] using wordTrace_append hprefix tailTrace_3449519
  have hstable : (prefixWord ++ tailWord_3449519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449519).length < 2 ^ (prefixWord ++ tailWord_3449519).sum := by decide
  have hdescent : baseEnd_3449519 < baseStart_3449519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449532 : List Nat := [2, 2, 2, 3, 1, 1, 2, 1, 3, 3, 3]
def baseStart_3449532 : Nat := 118140960795 + 3449532 * 2 ^ 59
def prefixEnd_3449532 : Nat := 4983230072969 + 3 ^ 40 * 3449532 * 2
def baseEnd_3449532 : Nat := 1771267949065302923885897

theorem tailTrace_3449532 : CollatzResearch.WordTrace tailWord_3449532 prefixEnd_3449532 1771267949065302923885897 := by
  unfold tailWord_3449532
  simp only [CollatzResearch.WordTrace]
  refine ⟨62907384069471086003711425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83876512092628114671615233 62907384069471086003711425)
  ·
    refine ⟨47180538052103314502783569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62907384069471086003711425 47180538052103314502783569)
    ·
      refine ⟨35385403539077485877087677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47180538052103314502783569 35385403539077485877087677)
      ·
        refine ⟨13269526327154057203907879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35385403539077485877087677 13269526327154057203907879)
        ·
          refine ⟨19904289490731085805861819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13269526327154057203907879 19904289490731085805861819)
          ·
            refine ⟨29856434236096628708792729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19904289490731085805861819 29856434236096628708792729)
            ·
              refine ⟨22392325677072471531594547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29856434236096628708792729 22392325677072471531594547)
              ·
                refine ⟨33588488515608707297391821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22392325677072471531594547 33588488515608707297391821)
                ·
                  refine ⟨12595683193353265236521933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33588488515608707297391821 12595683193353265236521933)
                  ·
                    refine ⟨4723381197507474463695725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12595683193353265236521933 4723381197507474463695725)
                    ·
                      refine ⟨1771267949065302923885897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4723381197507474463695725 1771267949065302923885897)
                      ·
                        rfl

theorem cell23_3449532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_3449532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3449532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3449532 prefixEnd_3449532 := by exact prefixLift 3449532
  have htrace : WordTrace (prefixWord ++ tailWord_3449532) baseStart_3449532 baseEnd_3449532 := by
    simpa [prefixWord, tailWord_3449532, baseEnd_3449532] using wordTrace_append hprefix tailTrace_3449532
  have hstable : (prefixWord ++ tailWord_3449532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449532).length < 2 ^ (prefixWord ++ tailWord_3449532).sum := by decide
  have hdescent : baseEnd_3449532 < baseStart_3449532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449533 : List Nat := [1, 4, 1, 2, 1, 3, 3, 3, 1, 2, 2]
def baseStart_3449533 : Nat := 118140960795 + 3449533 * 2 ^ 59
def prefixEnd_3449533 : Nat := 4983230072969 + 3 ^ 40 * 3449533 * 2
def baseEnd_3449533 : Nat := 1771268462545957419973393

theorem tailTrace_3449533 : CollatzResearch.WordTrace tailWord_3449533 prefixEnd_3449533 1771268462545957419973393 := by
  unfold tailWord_3449533
  simp only [CollatzResearch.WordTrace]
  refine ⟨125814804611938549178209253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83876536407959032785472835 125814804611938549178209253)
  ·
    refine ⟨23590275864738477970914235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125814804611938549178209253 23590275864738477970914235)
    ·
      refine ⟨35385413797107716956371353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23590275864738477970914235 35385413797107716956371353)
      ·
        refine ⟨26539060347830787717278515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35385413797107716956371353 26539060347830787717278515)
        ·
          refine ⟨39808590521746181575917773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26539060347830787717278515 39808590521746181575917773)
          ·
            refine ⟨14928221445654818090969165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39808590521746181575917773 14928221445654818090969165)
            ·
              refine ⟨5598083042120556784113437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14928221445654818090969165 5598083042120556784113437)
              ·
                refine ⟨2099281140795208794042539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5598083042120556784113437 2099281140795208794042539)
                ·
                  refine ⟨3148921711192813191063809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2099281140795208794042539 3148921711192813191063809)
                  ·
                    refine ⟨2361691283394609893297857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3148921711192813191063809 2361691283394609893297857)
                    ·
                      refine ⟨1771268462545957419973393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2361691283394609893297857 1771268462545957419973393)
                      ·
                        rfl

theorem cell23_3449533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 3, 1, 2, 2].length) (baseStart_3449533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3449533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3449533 prefixEnd_3449533 := by exact prefixLift 3449533
  have htrace : WordTrace (prefixWord ++ tailWord_3449533) baseStart_3449533 baseEnd_3449533 := by
    simpa [prefixWord, tailWord_3449533, baseEnd_3449533] using wordTrace_append hprefix tailTrace_3449533
  have hstable : (prefixWord ++ tailWord_3449533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449533).length < 2 ^ (prefixWord ++ tailWord_3449533).sum := by decide
  have hdescent : baseEnd_3449533 < baseStart_3449533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449550 : List Nat := [4, 1, 1, 1, 3, 3, 3, 2, 1, 2, 2]
def baseStart_3449550 : Nat := 118140960795 + 3449550 * 2 ^ 59
def prefixEnd_3449550 : Nat := 4983230072969 + 3 ^ 40 * 3449550 * 2
def baseEnd_3449550 : Nat := 1771277191717083853460815

theorem tailTrace_3449550 : CollatzResearch.WordTrace tailWord_3449550 prefixEnd_3449550 1771277191717083853460815 := by
  unfold tailWord_3449550
  simp only [CollatzResearch.WordTrace]
  refine ⟨15726928081609620135197263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83876949768584640721052069 15726928081609620135197263)
  ·
    refine ⟨23590392122414430202795895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15726928081609620135197263 23590392122414430202795895)
    ·
      refine ⟨35385588183621645304193843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23590392122414430202795895 35385588183621645304193843)
      ·
        refine ⟨53078382275432467956290765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35385588183621645304193843 53078382275432467956290765)
        ·
          refine ⟨19904393353287175483609037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53078382275432467956290765 19904393353287175483609037)
          ·
            refine ⟨7464147507482690806353389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19904393353287175483609037 7464147507482690806353389)
            ·
              refine ⟨2799055315306009052382521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7464147507482690806353389 2799055315306009052382521)
              ·
                refine ⟨2099291486479506789286891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2799055315306009052382521 2099291486479506789286891)
                ·
                  refine ⟨3148937229719260183930337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2099291486479506789286891 3148937229719260183930337)
                  ·
                    refine ⟨2361702922289445137947753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3148937229719260183930337 2361702922289445137947753)
                    ·
                      refine ⟨1771277191717083853460815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2361702922289445137947753 1771277191717083853460815)
                      ·
                        rfl

theorem cell23_3449550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 2, 1, 2, 2].length) (baseStart_3449550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3449550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3449550 prefixEnd_3449550 := by exact prefixLift 3449550
  have htrace : WordTrace (prefixWord ++ tailWord_3449550) baseStart_3449550 baseEnd_3449550 := by
    simpa [prefixWord, tailWord_3449550, baseEnd_3449550] using wordTrace_append hprefix tailTrace_3449550
  have hstable : (prefixWord ++ tailWord_3449550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449550).length < 2 ^ (prefixWord ++ tailWord_3449550).sum := by decide
  have hdescent : baseEnd_3449550 < baseStart_3449550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449576 : List Nat := [2, 1, 4, 1, 4, 1, 1, 1, 3, 3, 2]
def baseStart_3449576 : Nat := 118140960795 + 3449576 * 2 ^ 59
def prefixEnd_3449576 : Nat := 4983230072969 + 3 ^ 40 * 3449576 * 2
def baseEnd_3449576 : Nat := 1771290542214100751735695

theorem tailTrace_3449576 : CollatzResearch.WordTrace tailWord_3449576 prefixEnd_3449576 1771290542214100751735695 := by
  unfold tailWord_3449576
  simp only [CollatzResearch.WordTrace]
  refine ⟨62908186475391383761012291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83877581967188511681349721 62908186475391383761012291)
  ·
    refine ⟨94362279713087075641518437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62908186475391383761012291 94362279713087075641518437)
    ·
      refine ⟨17692927446203826682784707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94362279713087075641518437 17692927446203826682784707)
      ·
        refine ⟨26539391169305740024177061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17692927446203826682784707 26539391169305740024177061)
        ·
          refine ⟨4976135844244826254533199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26539391169305740024177061 4976135844244826254533199)
          ·
            refine ⟨7464203766367239381799799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4976135844244826254533199 7464203766367239381799799)
            ·
              refine ⟨11196305649550859072699699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7464203766367239381799799 11196305649550859072699699)
              ·
                refine ⟨16794458474326288609049549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11196305649550859072699699 16794458474326288609049549)
                ·
                  refine ⟨6297921927872358228393581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16794458474326288609049549 6297921927872358228393581)
                  ·
                    refine ⟨2361720722952134335647593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6297921927872358228393581 2361720722952134335647593)
                    ·
                      refine ⟨1771290542214100751735695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2361720722952134335647593 1771290542214100751735695)
                      ·
                        rfl

theorem cell23_3449576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 3, 3, 2].length) (baseStart_3449576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3449576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3449576 prefixEnd_3449576 := by exact prefixLift 3449576
  have htrace : WordTrace (prefixWord ++ tailWord_3449576) baseStart_3449576 baseEnd_3449576 := by
    simpa [prefixWord, tailWord_3449576, baseEnd_3449576] using wordTrace_append hprefix tailTrace_3449576
  have hstable : (prefixWord ++ tailWord_3449576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449576).length < 2 ^ (prefixWord ++ tailWord_3449576).sum := by decide
  have hdescent : baseEnd_3449576 < baseStart_3449576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449605 : List Nat := [1, 3, 1, 1, 2, 1, 1, 3, 1, 2, 7]
def baseStart_3449605 : Nat := 118140960795 + 3449605 * 2 ^ 59
def prefixEnd_3449605 : Nat := 4983230072969 + 3 ^ 40 * 3449605 * 2
def baseEnd_3449605 : Nat := 1771305433153081138273061

theorem tailTrace_3449605 : CollatzResearch.WordTrace tailWord_3449605 prefixEnd_3449605 1771305433153081138273061 := by
  unfold tailWord_3449605
  simp only [CollatzResearch.WordTrace]
  refine ⟨125817430667677705474830269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83878287111785136983220179 125817430667677705474830269)
  ·
    refine ⟨47181536500379139553061351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125817430667677705474830269 47181536500379139553061351)
    ·
      refine ⟨70772304750568709329592027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47181536500379139553061351 70772304750568709329592027)
      ·
        refine ⟨106158457125853063994388041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70772304750568709329592027 106158457125853063994388041)
        ·
          refine ⟨79618842844389797995791031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106158457125853063994388041 79618842844389797995791031)
          ·
            refine ⟨119428264266584696993686547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79618842844389797995791031 119428264266584696993686547)
            ·
              refine ⟨179142396399877045490529821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119428264266584696993686547 179142396399877045490529821)
              ·
                refine ⟨67178398649953892058948683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179142396399877045490529821 67178398649953892058948683)
                ·
                  refine ⟨100767597974930838088423025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67178398649953892058948683 100767597974930838088423025)
                  ·
                    refine ⟨75575698481198128566317269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 100767597974930838088423025 75575698481198128566317269)
                    ·
                      refine ⟨1771305433153081138273061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 75575698481198128566317269 1771305433153081138273061)
                      ·
                        rfl

theorem cell23_3449605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 2, 7].length) (baseStart_3449605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3449605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3449605 prefixEnd_3449605 := by exact prefixLift 3449605
  have htrace : WordTrace (prefixWord ++ tailWord_3449605) baseStart_3449605 baseEnd_3449605 := by
    simpa [prefixWord, tailWord_3449605, baseEnd_3449605] using wordTrace_append hprefix tailTrace_3449605
  have hstable : (prefixWord ++ tailWord_3449605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449605).length < 2 ^ (prefixWord ++ tailWord_3449605).sum := by decide
  have hdescent : baseEnd_3449605 < baseStart_3449605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449646 : List Nat := [4, 1, 3, 2, 1, 1, 1, 5, 5]
def baseStart_3449646 : Nat := 118140960795 + 3449646 * 2 ^ 59
def prefixEnd_3449646 : Nat := 4983230072969 + 3 ^ 40 * 3449646 * 2
def baseEnd_3449646 : Nat := 196814053984435053095597

theorem tailTrace_3449646 : CollatzResearch.WordTrace tailWord_3449646 prefixEnd_3449646 196814053984435053095597 := by
  unfold tailWord_3449646
  simp only [CollatzResearch.WordTrace]
  refine ⟨15727365757566146184634099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83879284040352779651381861 15727365757566146184634099)
  ·
    refine ⟨23591048636349219276951149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15727365757566146184634099 23591048636349219276951149)
    ·
      refine ⟨8846643238630957228856681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23591048636349219276951149 8846643238630957228856681)
      ·
        refine ⟨6634982428973217921642511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8846643238630957228856681 6634982428973217921642511)
        ·
          refine ⟨9952473643459826882463767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6634982428973217921642511 9952473643459826882463767)
          ·
            refine ⟨14928710465189740323695651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9952473643459826882463767 14928710465189740323695651)
            ·
              refine ⟨22393065697784610485543477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14928710465189740323695651 22393065697784610485543477)
              ·
                refine ⟨2099349909167307233019701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22393065697784610485543477 2099349909167307233019701)
                ·
                  refine ⟨196814053984435053095597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2099349909167307233019701 196814053984435053095597)
                  ·
                    rfl

theorem cell23_3449646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 5, 5].length) (baseStart_3449646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3449646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3449646 prefixEnd_3449646 := by exact prefixLift 3449646
  have htrace : WordTrace (prefixWord ++ tailWord_3449646) baseStart_3449646 baseEnd_3449646 := by
    simpa [prefixWord, tailWord_3449646, baseEnd_3449646] using wordTrace_append hprefix tailTrace_3449646
  have hstable : (prefixWord ++ tailWord_3449646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449646).length < 2 ^ (prefixWord ++ tailWord_3449646).sum := by decide
  have hdescent : baseEnd_3449646 < baseStart_3449646 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449689 : List Nat := [1, 2, 1, 2, 2, 4, 2, 2, 3, 4]
def baseStart_3449689 : Nat := 118140960795 + 3449689 * 2 ^ 59
def prefixEnd_3449689 : Nat := 4983230072969 + 3 ^ 40 * 3449689 * 2
def baseEnd_3449689 : Nat := 590449521842686269874225

theorem tailTrace_3449689 : CollatzResearch.WordTrace tailWord_3449689 prefixEnd_3449689 590449521842686269874225 := by
  unfold tailWord_3449689
  simp only [CollatzResearch.WordTrace]
  refine ⟨125820494399373387820888121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83880329599582258547258747 125820494399373387820888121)
  ·
    refine ⟨94365370799530040865666091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125820494399373387820888121 94365370799530040865666091)
    ·
      refine ⟨141548056199295061298499137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94365370799530040865666091 141548056199295061298499137)
      ·
        refine ⟨106161042149471295973874353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141548056199295061298499137 106161042149471295973874353)
        ·
          refine ⟨79620781612103471980405765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106161042149471295973874353 79620781612103471980405765)
          ·
            refine ⟨14928896552269400996326081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79620781612103471980405765 14928896552269400996326081)
            ·
              refine ⟨11196672414202050747244561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14928896552269400996326081 11196672414202050747244561)
              ·
                refine ⟨8397504310651538060433421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11196672414202050747244561 8397504310651538060433421)
                ·
                  refine ⟨3149064116494326772662533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8397504310651538060433421 3149064116494326772662533)
                  ·
                    refine ⟨590449521842686269874225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3149064116494326772662533 590449521842686269874225)
                    ·
                      rfl

theorem cell23_3449689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 3, 4].length) (baseStart_3449689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3449689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3449689 prefixEnd_3449689 := by exact prefixLift 3449689
  have htrace : WordTrace (prefixWord ++ tailWord_3449689) baseStart_3449689 baseEnd_3449689 := by
    simpa [prefixWord, tailWord_3449689, baseEnd_3449689] using wordTrace_append hprefix tailTrace_3449689
  have hstable : (prefixWord ++ tailWord_3449689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449689).length < 2 ^ (prefixWord ++ tailWord_3449689).sum := by decide
  have hdescent : baseEnd_3449689 < baseStart_3449689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449699 : List Nat := [1, 1, 1, 5, 3, 1, 2, 1, 1, 4, 3]
def baseStart_3449699 : Nat := 118140960795 + 3449699 * 2 ^ 59
def prefixEnd_3449699 : Nat := 4983230072969 + 3 ^ 40 * 3449699 * 2
def baseEnd_3449699 : Nat := 1771353700334603770497629

theorem tailTrace_3449699 : CollatzResearch.WordTrace tailWord_3449699 prefixEnd_3449699 1771353700334603770497629 := by
  unfold tailWord_3449699
  simp only [CollatzResearch.WordTrace]
  refine ⟨125820859129337159528752151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83880572752891439685834767 125820859129337159528752151)
  ·
    refine ⟨188731288694005739293128227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125820859129337159528752151 188731288694005739293128227)
    ·
      refine ⟨283096933041008608939692341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188731288694005739293128227 283096933041008608939692341)
      ·
        refine ⟨26540337472594557088096157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 283096933041008608939692341 26540337472594557088096157)
        ·
          refine ⟨9952626552222958908036059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26540337472594557088096157 9952626552222958908036059)
          ·
            refine ⟨14928939828334438362054089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9952626552222958908036059 14928939828334438362054089)
            ·
              refine ⟨11196704871250828771540567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14928939828334438362054089 11196704871250828771540567)
              ·
                refine ⟨16795057306876243157310851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11196704871250828771540567 16795057306876243157310851)
                ·
                  refine ⟨25192585960314364735966277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16795057306876243157310851 25192585960314364735966277)
                  ·
                    refine ⟨4723609867558943387993677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25192585960314364735966277 4723609867558943387993677)
                    ·
                      refine ⟨1771353700334603770497629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4723609867558943387993677 1771353700334603770497629)
                      ·
                        rfl

theorem cell23_3449699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_3449699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3449699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3449699 prefixEnd_3449699 := by exact prefixLift 3449699
  have htrace : WordTrace (prefixWord ++ tailWord_3449699) baseStart_3449699 baseEnd_3449699 := by
    simpa [prefixWord, tailWord_3449699, baseEnd_3449699] using wordTrace_append hprefix tailTrace_3449699
  have hstable : (prefixWord ++ tailWord_3449699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449699).length < 2 ^ (prefixWord ++ tailWord_3449699).sum := by decide
  have hdescent : baseEnd_3449699 < baseStart_3449699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449732 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 2, 9]
def baseStart_3449732 : Nat := 118140960795 + 3449732 * 2 ^ 59
def prefixEnd_3449732 : Nat := 4983230072969 + 3 ^ 40 * 3449732 * 2
def baseEnd_3449732 : Nat := 590456881732067380461659

theorem tailTrace_3449732 : CollatzResearch.WordTrace tailWord_3449732 prefixEnd_3449732 590456881732067380461659 := by
  unfold tailWord_3449732
  simp only [CollatzResearch.WordTrace]
  refine ⟨62911031369108803082351725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83881375158811737443135633 62911031369108803082351725)
  ·
    refine ⟨23591636763415801155881897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62911031369108803082351725 23591636763415801155881897)
    ·
      refine ⟨17693727572561850866911423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23591636763415801155881897 17693727572561850866911423)
      ·
        refine ⟨26540591358842776300367135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17693727572561850866911423 26540591358842776300367135)
        ·
          refine ⟨39810887038264164450550703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26540591358842776300367135 39810887038264164450550703)
          ·
            refine ⟨59716330557396246675826055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39810887038264164450550703 59716330557396246675826055)
            ·
              refine ⟨89574495836094370013739083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59716330557396246675826055 89574495836094370013739083)
              ·
                refine ⟨134361743754141555020608625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89574495836094370013739083 134361743754141555020608625)
                ·
                  refine ⟨100771307815606166265456469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134361743754141555020608625 100771307815606166265456469)
                  ·
                    refine ⟨590456881732067380461659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 100771307815606166265456469 590456881732067380461659)
                    ·
                      rfl

theorem cell23_3449732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_3449732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3449732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3449732 prefixEnd_3449732 := by exact prefixLift 3449732
  have htrace : WordTrace (prefixWord ++ tailWord_3449732) baseStart_3449732 baseEnd_3449732 := by
    simpa [prefixWord, tailWord_3449732, baseEnd_3449732] using wordTrace_append hprefix tailTrace_3449732
  have hstable : (prefixWord ++ tailWord_3449732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449732).length < 2 ^ (prefixWord ++ tailWord_3449732).sum := by decide
  have hdescent : baseEnd_3449732 < baseStart_3449732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449736 : List Nat := [2, 1, 3, 3, 2, 1, 4, 1, 6]
def baseStart_3449736 : Nat := 118140960795 + 3449736 * 2 ^ 59
def prefixEnd_3449736 : Nat := 4983230072969 + 3 ^ 40 * 3449736 * 2
def baseEnd_3449736 : Nat := 196819188790980013970551

theorem tailTrace_3449736 : CollatzResearch.WordTrace tailWord_3449736 prefixEnd_3449736 196819188790980013970551 := by
  unfold tailWord_3449736
  simp only [CollatzResearch.WordTrace]
  refine ⟨62911104315101557423924531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83881472420135409898566041 62911104315101557423924531)
  ·
    refine ⟨94366656472652336135886797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62911104315101557423924531 94366656472652336135886797)
    ·
      refine ⟨35387496177244626050957549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94366656472652336135886797 35387496177244626050957549)
      ·
        refine ⟨13270311066466734769109081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35387496177244626050957549 13270311066466734769109081)
        ·
          refine ⟨9952733299850051076831811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13270311066466734769109081 9952733299850051076831811)
          ·
            refine ⟨14929099949775076615247717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9952733299850051076831811 14929099949775076615247717)
            ·
              refine ⟨2799206240582826865358947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14929099949775076615247717 2799206240582826865358947)
              ·
                refine ⟨4198809360874240298038421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2799206240582826865358947 4198809360874240298038421)
                ·
                  refine ⟨196819188790980013970551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4198809360874240298038421 196819188790980013970551)
                  ·
                    rfl

theorem cell23_3449736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 1, 6].length) (baseStart_3449736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3449736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3449736 prefixEnd_3449736 := by exact prefixLift 3449736
  have htrace : WordTrace (prefixWord ++ tailWord_3449736) baseStart_3449736 baseEnd_3449736 := by
    simpa [prefixWord, tailWord_3449736, baseEnd_3449736] using wordTrace_append hprefix tailTrace_3449736
  have hstable : (prefixWord ++ tailWord_3449736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449736).length < 2 ^ (prefixWord ++ tailWord_3449736).sum := by decide
  have hdescent : baseEnd_3449736 < baseStart_3449736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449739 : List Nat := [1, 1, 1, 1, 4, 2, 2, 1, 3, 5, 2]
def baseStart_3449739 : Nat := 118140960795 + 3449739 * 2 ^ 59
def prefixEnd_3449739 : Nat := 4983230072969 + 3 ^ 40 * 3449739 * 2
def baseEnd_3449739 : Nat := 1771374239560783613997445

theorem tailTrace_3449739 : CollatzResearch.WordTrace tailWord_3449739 prefixEnd_3449739 1771374239560783613997445 := by
  unfold tailWord_3449739
  simp only [CollatzResearch.WordTrace]
  refine ⟨125822318049192246360208271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83881545366128164240138847 125822318049192246360208271)
  ·
    refine ⟨188733477073788369540312407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125822318049192246360208271 188733477073788369540312407)
    ·
      refine ⟨283100215610682554310468611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188733477073788369540312407 283100215610682554310468611)
      ·
        refine ⟨424650323416023831465702917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283100215610682554310468611 424650323416023831465702917)
        ·
          refine ⟨79621935640504468399819297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 424650323416023831465702917 79621935640504468399819297)
          ·
            refine ⟨59716451730378351299864473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79621935640504468399819297 59716451730378351299864473)
            ·
              refine ⟨44787338797783763474898355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59716451730378351299864473 44787338797783763474898355)
              ·
                refine ⟨67181008196675645212347533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44787338797783763474898355 67181008196675645212347533)
                ·
                  refine ⟨25192878073753366954630325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67181008196675645212347533 25192878073753366954630325)
                  ·
                    refine ⟨2361832319414378151996593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25192878073753366954630325 2361832319414378151996593)
                    ·
                      refine ⟨1771374239560783613997445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2361832319414378151996593 1771374239560783613997445)
                      ·
                        rfl

theorem cell23_3449739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 5, 2].length) (baseStart_3449739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3449739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3449739 prefixEnd_3449739 := by exact prefixLift 3449739
  have htrace : WordTrace (prefixWord ++ tailWord_3449739) baseStart_3449739 baseEnd_3449739 := by
    simpa [prefixWord, tailWord_3449739, baseEnd_3449739] using wordTrace_append hprefix tailTrace_3449739
  have hstable : (prefixWord ++ tailWord_3449739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449739).length < 2 ^ (prefixWord ++ tailWord_3449739).sum := by decide
  have hdescent : baseEnd_3449739 < baseStart_3449739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449749 : List Nat := [1, 3, 2, 1, 1, 5, 1, 1, 3, 5]
def baseStart_3449749 : Nat := 118140960795 + 3449749 * 2 ^ 59
def prefixEnd_3449749 : Nat := 4983230072969 + 3 ^ 40 * 3449749 * 2
def baseEnd_3449749 : Nat := 590459791455776191624133

theorem tailTrace_3449749 : CollatzResearch.WordTrace tailWord_3449749 prefixEnd_3449749 590459791455776191624133 := by
  unfold tailWord_3449749
  simp only [CollatzResearch.WordTrace]
  refine ⟨125822682779156018068072301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83881788519437345378714867 125822682779156018068072301)
  ·
    refine ⟨47183506042183506775527113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125822682779156018068072301 47183506042183506775527113)
    ·
      refine ⟨35387629531637630081645335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47183506042183506775527113 35387629531637630081645335)
      ·
        refine ⟨53081444297456445122468003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35387629531637630081645335 53081444297456445122468003)
        ·
          refine ⟨79622166446184667683702005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53081444297456445122468003 79622166446184667683702005)
          ·
            refine ⟨7464578104329812595347063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79622166446184667683702005 7464578104329812595347063)
            ·
              refine ⟨11196867156494718893020595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7464578104329812595347063 11196867156494718893020595)
              ·
                refine ⟨16795300734742078339530893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11196867156494718893020595 16795300734742078339530893)
                ·
                  refine ⟨6298237775528279377324085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16795300734742078339530893 6298237775528279377324085)
                  ·
                    refine ⟨590459791455776191624133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6298237775528279377324085 590459791455776191624133)
                    ·
                      rfl

theorem cell23_3449749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 3, 5].length) (baseStart_3449749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3449749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3449749 prefixEnd_3449749 := by exact prefixLift 3449749
  have htrace : WordTrace (prefixWord ++ tailWord_3449749) baseStart_3449749 baseEnd_3449749 := by
    simpa [prefixWord, tailWord_3449749, baseEnd_3449749] using wordTrace_append hprefix tailTrace_3449749
  have hstable : (prefixWord ++ tailWord_3449749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449749).length < 2 ^ (prefixWord ++ tailWord_3449749).sum := by decide
  have hdescent : baseEnd_3449749 < baseStart_3449749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449750 : List Nat := [5, 3, 1, 1, 1, 1, 1, 3, 2, 2, 3]
def baseStart_3449750 : Nat := 118140960795 + 3449750 * 2 ^ 59
def prefixEnd_3449750 : Nat := 4983230072969 + 3 ^ 40 * 3449750 * 2
def baseEnd_3449750 : Nat := 1771379887847983070959895

theorem tailTrace_3449750 : CollatzResearch.WordTrace tailWord_3449750 prefixEnd_3449750 1771379887847983070959895 := by
  unfold tailWord_3449750
  simp only [CollatzResearch.WordTrace]
  refine ⟨7863919953259524702428669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83881812834768263492572469 7863919953259524702428669)
  ·
    refine ⟨2948969982472321763410751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7863919953259524702428669 2948969982472321763410751)
    ·
      refine ⟨4423454973708482645116127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2948969982472321763410751 4423454973708482645116127)
      ·
        refine ⟨6635182460562723967674191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4423454973708482645116127 6635182460562723967674191)
        ·
          refine ⟨9952773690844085951511287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6635182460562723967674191 9952773690844085951511287)
          ·
            refine ⟨14929160536266128927266931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9952773690844085951511287 14929160536266128927266931)
            ·
              refine ⟨22393740804399193390900397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14929160536266128927266931 22393740804399193390900397)
              ·
                refine ⟨8397652801649697521587649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22393740804399193390900397 8397652801649697521587649)
                ·
                  refine ⟨6298239601237273141190737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8397652801649697521587649 6298239601237273141190737)
                  ·
                    refine ⟨4723679700927954855893053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6298239601237273141190737 4723679700927954855893053)
                    ·
                      refine ⟨1771379887847983070959895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4723679700927954855893053 1771379887847983070959895)
                      ·
                        rfl

theorem cell23_3449750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_3449750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3449750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3449750 prefixEnd_3449750 := by exact prefixLift 3449750
  have htrace : WordTrace (prefixWord ++ tailWord_3449750) baseStart_3449750 baseEnd_3449750 := by
    simpa [prefixWord, tailWord_3449750, baseEnd_3449750] using wordTrace_append hprefix tailTrace_3449750
  have hstable : (prefixWord ++ tailWord_3449750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449750).length < 2 ^ (prefixWord ++ tailWord_3449750).sum := by decide
  have hdescent : baseEnd_3449750 < baseStart_3449750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449799 : List Nat := [1, 1, 4, 1, 1, 2, 3, 3, 1, 2, 4]
def baseStart_3449799 : Nat := 118140960795 + 3449799 * 2 ^ 59
def prefixEnd_3449799 : Nat := 4983230072969 + 3 ^ 40 * 3449799 * 2
def baseEnd_3449799 : Nat := 1771405048400053379247169

theorem tailTrace_3449799 : CollatzResearch.WordTrace tailWord_3449799 prefixEnd_3449799 1771405048400053379247169 := by
  unfold tailWord_3449799
  simp only [CollatzResearch.WordTrace]
  refine ⟨125824506428974876607392451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83883004285983251071594967 125824506428974876607392451)
  ·
    refine ⟨188736759643462314911088677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125824506428974876607392451 188736759643462314911088677)
    ·
      refine ⟨35388142433149184045829127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188736759643462314911088677 35388142433149184045829127)
      ·
        refine ⟨53082213649723776068743691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35388142433149184045829127 53082213649723776068743691)
        ·
          refine ⟨79623320474585664103115537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53082213649723776068743691 79623320474585664103115537)
          ·
            refine ⟨59717490355939248077336653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79623320474585664103115537 59717490355939248077336653)
            ·
              refine ⟨22394058883477218029001245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59717490355939248077336653 22394058883477218029001245)
              ·
                refine ⟨8397772081303956760875467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22394058883477218029001245 8397772081303956760875467)
                ·
                  refine ⟨12596658121955935141313201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8397772081303956760875467 12596658121955935141313201)
                  ·
                    refine ⟨9447493591466951355984901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12596658121955935141313201 9447493591466951355984901)
                    ·
                      refine ⟨1771405048400053379247169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9447493591466951355984901 1771405048400053379247169)
                      ·
                        rfl

theorem cell23_3449799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_3449799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3449799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3449799 prefixEnd_3449799 := by exact prefixLift 3449799
  have htrace : WordTrace (prefixWord ++ tailWord_3449799) baseStart_3449799 baseEnd_3449799 := by
    simpa [prefixWord, tailWord_3449799, baseEnd_3449799] using wordTrace_append hprefix tailTrace_3449799
  have hstable : (prefixWord ++ tailWord_3449799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449799).length < 2 ^ (prefixWord ++ tailWord_3449799).sum := by decide
  have hdescent : baseEnd_3449799 < baseStart_3449799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449803 : List Nat := [1, 1, 1, 1, 3, 6, 1, 2, 3, 2, 2]
def baseStart_3449803 : Nat := 118140960795 + 3449803 * 2 ^ 59
def prefixEnd_3449803 : Nat := 4983230072969 + 3 ^ 40 * 3449803 * 2
def baseEnd_3449803 : Nat := 1771407102322671363597151

theorem tailTrace_3449803 : CollatzResearch.WordTrace tailWord_3449803 prefixEnd_3449803 1771407102322671363597151 := by
  unfold tailWord_3449803
  simp only [CollatzResearch.WordTrace]
  refine ⟨125824652320960385290538063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83883101547306923527025375 125824652320960385290538063)
  ·
    refine ⟨188736978481440577935807095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125824652320960385290538063 188736978481440577935807095)
    ·
      refine ⟨283105467722160866903710643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188736978481440577935807095 283105467722160866903710643)
      ·
        refine ⟨424658201583241300355565965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283105467722160866903710643 424658201583241300355565965)
        ·
          refine ⟨159246825593715487633337237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 424658201583241300355565965 159246825593715487633337237)
          ·
            refine ⟨7464694949705413482812683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 159246825593715487633337237 7464694949705413482812683)
            ·
              refine ⟨11197042424558120224219025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7464694949705413482812683 11197042424558120224219025)
              ·
                refine ⟨8397781818418590168164269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11197042424558120224219025 8397781818418590168164269)
                ·
                  refine ⟨3149168181906971313061601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8397781818418590168164269 3149168181906971313061601)
                  ·
                    refine ⟨2361876136430228484796201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3149168181906971313061601 2361876136430228484796201)
                    ·
                      refine ⟨1771407102322671363597151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2361876136430228484796201 1771407102322671363597151)
                      ·
                        rfl

theorem cell23_3449803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 3, 2, 2].length) (baseStart_3449803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3449803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3449803 prefixEnd_3449803 := by exact prefixLift 3449803
  have htrace : WordTrace (prefixWord ++ tailWord_3449803) baseStart_3449803 baseEnd_3449803 := by
    simpa [prefixWord, tailWord_3449803, baseEnd_3449803] using wordTrace_append hprefix tailTrace_3449803
  have hstable : (prefixWord ++ tailWord_3449803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449803).length < 2 ^ (prefixWord ++ tailWord_3449803).sum := by decide
  have hdescent : baseEnd_3449803 < baseStart_3449803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449806 : List Nat := [4, 1, 1, 1, 2, 3, 2, 1, 3, 2, 3]
def baseStart_3449806 : Nat := 118140960795 + 3449806 * 2 ^ 59
def prefixEnd_3449806 : Nat := 4983230072969 + 3 ^ 40 * 3449806 * 2
def baseEnd_3449806 : Nat := 1771408642764634851859637

theorem tailTrace_3449806 : CollatzResearch.WordTrace tailWord_3449806 prefixEnd_3449806 1771408642764634851859637 := by
  unfold tailWord_3449806
  simp only [CollatzResearch.WordTrace]
  refine ⟨15728095217493689600362159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83883174493299677868598181 15728095217493689600362159)
  ·
    refine ⟨23592142826240534400543239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15728095217493689600362159 23592142826240534400543239)
    ·
      refine ⟨35388214239360801600814859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23592142826240534400543239 35388214239360801600814859)
      ·
        refine ⟨53082321359041202401222289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35388214239360801600814859 53082321359041202401222289)
        ·
          refine ⟨39811741019280901800916717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53082321359041202401222289 39811741019280901800916717)
          ·
            refine ⟨14929402882230338175343769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39811741019280901800916717 14929402882230338175343769)
            ·
              refine ⟨11197052161672753631507827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14929402882230338175343769 11197052161672753631507827)
              ·
                refine ⟨16795578242509130447261741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11197052161672753631507827 16795578242509130447261741)
                ·
                  refine ⟨6298341840940923917723153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16795578242509130447261741 6298341840940923917723153)
                  ·
                    refine ⟨4723756380705692938292365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6298341840940923917723153 4723756380705692938292365)
                    ·
                      refine ⟨1771408642764634851859637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4723756380705692938292365 1771408642764634851859637)
                      ·
                        rfl

theorem cell23_3449806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 3, 2, 3].length) (baseStart_3449806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3449806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3449806 prefixEnd_3449806 := by exact prefixLift 3449806
  have htrace : WordTrace (prefixWord ++ tailWord_3449806) baseStart_3449806 baseEnd_3449806 := by
    simpa [prefixWord, tailWord_3449806, baseEnd_3449806] using wordTrace_append hprefix tailTrace_3449806
  have hstable : (prefixWord ++ tailWord_3449806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449806).length < 2 ^ (prefixWord ++ tailWord_3449806).sum := by decide
  have hdescent : baseEnd_3449806 < baseStart_3449806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449809 : List Nat := [1, 2, 2, 1, 2, 1, 7, 7]
def baseStart_3449809 : Nat := 118140960795 + 3449809 * 2 ^ 59
def prefixEnd_3449809 : Nat := 4983230072969 + 3 ^ 40 * 3449809 * 2
def baseEnd_3449809 : Nat := 65607784563207345930449

theorem tailTrace_3449809 : CollatzResearch.WordTrace tailWord_3449809 prefixEnd_3449809 65607784563207345930449 := by
  unfold tailWord_3449809
  simp only [CollatzResearch.WordTrace]
  refine ⟨125824871158938648315256481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83883247439292432210170987 125824871158938648315256481)
  ·
    refine ⟨94368653369203986236442361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125824871158938648315256481 94368653369203986236442361)
    ·
      refine ⟨70776490026902989677331771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94368653369203986236442361 70776490026902989677331771)
      ·
        refine ⟨106164735040354484515997657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70776490026902989677331771 106164735040354484515997657)
        ·
          refine ⟨79623551280265863386998243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106164735040354484515997657 79623551280265863386998243)
          ·
            refine ⟨119435326920398795080497365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79623551280265863386998243 119435326920398795080497365)
            ·
              refine ⟨2799265474696846759699157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 119435326920398795080497365 2799265474696846759699157)
              ·
                refine ⟨65607784563207345930449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2799265474696846759699157 65607784563207345930449)
                ·
                  rfl

theorem cell23_3449809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 7].length) (baseStart_3449809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3449809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3449809 prefixEnd_3449809 := by exact prefixLift 3449809
  have htrace : WordTrace (prefixWord ++ tailWord_3449809) baseStart_3449809 baseEnd_3449809 := by
    simpa [prefixWord, tailWord_3449809, baseEnd_3449809] using wordTrace_append hprefix tailTrace_3449809
  have hstable : (prefixWord ++ tailWord_3449809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449809).length < 2 ^ (prefixWord ++ tailWord_3449809).sum := by decide
  have hdescent : baseEnd_3449809 < baseStart_3449809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449823 : List Nat := [1, 1, 2, 3, 5, 1, 1, 3, 1, 2, 3]
def baseStart_3449823 : Nat := 118140960795 + 3449823 * 2 ^ 59
def prefixEnd_3449823 : Nat := 4983230072969 + 3 ^ 40 * 3449823 * 2
def baseEnd_3449823 : Nat := 1771417371935761285347059

theorem tailTrace_3449823 : CollatzResearch.WordTrace tailWord_3449823 prefixEnd_3449823 1771417371935761285347059 := by
  unfold tailWord_3449823
  simp only [CollatzResearch.WordTrace]
  refine ⟨125825381780887928706266123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83883587853925285804177415 125825381780887928706266123)
  ·
    refine ⟨188738072671331893059399185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125825381780887928706266123 188738072671331893059399185)
    ·
      refine ⟨141553554503498919794549389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188738072671331893059399185 141553554503498919794549389)
      ·
        refine ⟨53082582938812094922956021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141553554503498919794549389 53082582938812094922956021)
        ·
          refine ⟨4976492150513633899027127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53082582938812094922956021 4976492150513633899027127)
          ·
            refine ⟨7464738225770450848540691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4976492150513633899027127 7464738225770450848540691)
            ·
              refine ⟨11197107338655676272811037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7464738225770450848540691 11197107338655676272811037)
              ·
                refine ⟨4198915251995878602304139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11197107338655676272811037 4198915251995878602304139)
                ·
                  refine ⟨6298372877993817903456209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4198915251995878602304139 6298372877993817903456209)
                  ·
                    refine ⟨4723779658495363427592157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6298372877993817903456209 4723779658495363427592157)
                    ·
                      refine ⟨1771417371935761285347059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4723779658495363427592157 1771417371935761285347059)
                      ·
                        rfl

theorem cell23_3449823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 3, 1, 2, 3].length) (baseStart_3449823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3449823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3449823 prefixEnd_3449823 := by exact prefixLift 3449823
  have htrace : WordTrace (prefixWord ++ tailWord_3449823) baseStart_3449823 baseEnd_3449823 := by
    simpa [prefixWord, tailWord_3449823, baseEnd_3449823] using wordTrace_append hprefix tailTrace_3449823
  have hstable : (prefixWord ++ tailWord_3449823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449823).length < 2 ^ (prefixWord ++ tailWord_3449823).sum := by decide
  have hdescent : baseEnd_3449823 < baseStart_3449823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449826 : List Nat := [3, 3, 3, 1, 1, 2, 10]
def baseStart_3449826 : Nat := 118140960795 + 3449826 * 2 ^ 59
def prefixEnd_3449826 : Nat := 4983230072969 + 3 ^ 40 * 3449826 * 2
def baseEnd_3449826 : Nat := 21869369288613886093945

theorem tailTrace_3449826 : CollatzResearch.WordTrace tailWord_3449826 prefixEnd_3449826 21869369288613886093945 := by
  unfold tailWord_3449826
  simp only [CollatzResearch.WordTrace]
  refine ⟨31456372799969265054656333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83883660799918040145750221 31456372799969265054656333)
  ·
    refine ⟨11796139799988474395496125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31456372799969265054656333 11796139799988474395496125)
    ·
      refine ⟨4423552424995677898311047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11796139799988474395496125 4423552424995677898311047)
      ·
        refine ⟨6635328637493516847466571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4423552424995677898311047 6635328637493516847466571)
        ·
          refine ⟨9952992956240275271199857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6635328637493516847466571 9952992956240275271199857)
          ·
            refine ⟨7464744717180206453399893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9952992956240275271199857 7464744717180206453399893)
            ·
              refine ⟨21869369288613886093945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7464744717180206453399893 21869369288613886093945)
              ·
                rfl

theorem cell23_3449826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 10].length) (baseStart_3449826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3449826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3449826 prefixEnd_3449826 := by exact prefixLift 3449826
  have htrace : WordTrace (prefixWord ++ tailWord_3449826) baseStart_3449826 baseEnd_3449826 := by
    simpa [prefixWord, tailWord_3449826, baseEnd_3449826] using wordTrace_append hprefix tailTrace_3449826
  have hstable : (prefixWord ++ tailWord_3449826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449826).length < 2 ^ (prefixWord ++ tailWord_3449826).sum := by decide
  have hdescent : baseEnd_3449826 < baseStart_3449826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449893 : List Nat := [1, 3, 1, 2, 2, 2, 1, 3, 4, 2, 2]
def baseStart_3449893 : Nat := 118140960795 + 3449893 * 2 ^ 59
def prefixEnd_3449893 : Nat := 4983230072969 + 3 ^ 40 * 3449893 * 2
def baseEnd_3449893 : Nat := 1771453315581576011471737

theorem tailTrace_3449893 : CollatzResearch.WordTrace tailWord_3449893 prefixEnd_3449893 1771453315581576011471737 := by
  unfold tailWord_3449893
  simp only [CollatzResearch.WordTrace]
  refine ⟨125827934890634330661314333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83885289927089553774209555 125827934890634330661314333)
  ·
    refine ⟨47185475583987873997992875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125827934890634330661314333 47185475583987873997992875)
    ·
      refine ⟨70778213375981810996989313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47185475583987873997992875 70778213375981810996989313)
      ·
        refine ⟨53083660031986358247741985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70778213375981810996989313 53083660031986358247741985)
        ·
          refine ⟨39812745023989768685806489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53083660031986358247741985 39812745023989768685806489)
          ·
            refine ⟨29859558767992326514354867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39812745023989768685806489 29859558767992326514354867)
            ·
              refine ⟨44789338151988489771532301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29859558767992326514354867 44789338151988489771532301)
              ·
                refine ⟨16796001806995683664324613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44789338151988489771532301 16796001806995683664324613)
                ·
                  refine ⟨3149250338811690687060865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16796001806995683664324613 3149250338811690687060865)
                  ·
                    refine ⟨2361937754108768015295649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3149250338811690687060865 2361937754108768015295649)
                    ·
                      refine ⟨1771453315581576011471737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2361937754108768015295649 1771453315581576011471737)
                      ·
                        rfl

theorem cell23_3449893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 4, 2, 2].length) (baseStart_3449893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3449893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3449893 prefixEnd_3449893 := by exact prefixLift 3449893
  have htrace : WordTrace (prefixWord ++ tailWord_3449893) baseStart_3449893 baseEnd_3449893 := by
    simpa [prefixWord, tailWord_3449893, baseEnd_3449893] using wordTrace_append hprefix tailTrace_3449893
  have hstable : (prefixWord ++ tailWord_3449893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449893).length < 2 ^ (prefixWord ++ tailWord_3449893).sum := by decide
  have hdescent : baseEnd_3449893 < baseStart_3449893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449936 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 4, 5, 2]
def baseStart_3449936 : Nat := 118140960795 + 3449936 * 2 ^ 59
def prefixEnd_3449936 : Nat := 4983230072969 + 3 ^ 40 * 3449936 * 2
def baseEnd_3449936 : Nat := 1771475395249719343234039

theorem tailTrace_3449936 : CollatzResearch.WordTrace tailWord_3449936 prefixEnd_3449936 1771475395249719343234039 := by
  unfold tailWord_3449936
  simp only [CollatzResearch.WordTrace]
  refine ⟨62914751614739274502564831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83886335486319032670086441 62914751614739274502564831)
  ·
    refine ⟨94372127422108911753847247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62914751614739274502564831 94372127422108911753847247)
    ·
      refine ⟨141558191133163367630770871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94372127422108911753847247 141558191133163367630770871)
      ·
        refine ⟨212337286699745051446156307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141558191133163367630770871 212337286699745051446156307)
        ·
          refine ⟨318505930049617577169234461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212337286699745051446156307 318505930049617577169234461)
          ·
            refine ⟨119439723768606591438462923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 318505930049617577169234461 119439723768606591438462923)
            ·
              refine ⟨179159585652909887157694385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119439723768606591438462923 179159585652909887157694385)
              ·
                refine ⟨134369689239682415368270789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179159585652909887157694385 134369689239682415368270789)
                ·
                  refine ⟨25194316732440452881550773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 134369689239682415368270789 25194316732440452881550773)
                  ·
                    refine ⟨2361967193666292457645385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25194316732440452881550773 2361967193666292457645385)
                    ·
                      refine ⟨1771475395249719343234039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2361967193666292457645385 1771475395249719343234039)
                      ·
                        rfl

theorem cell23_3449936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 4, 5, 2].length) (baseStart_3449936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3449936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3449936 prefixEnd_3449936 := by exact prefixLift 3449936
  have htrace : WordTrace (prefixWord ++ tailWord_3449936) baseStart_3449936 baseEnd_3449936 := by
    simpa [prefixWord, tailWord_3449936, baseEnd_3449936] using wordTrace_append hprefix tailTrace_3449936
  have hstable : (prefixWord ++ tailWord_3449936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449936).length < 2 ^ (prefixWord ++ tailWord_3449936).sum := by decide
  have hdescent : baseEnd_3449936 < baseStart_3449936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449939 : List Nat := [1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 5]
def baseStart_3449939 : Nat := 118140960795 + 3449939 * 2 ^ 59
def prefixEnd_3449939 : Nat := 4983230072969 + 3 ^ 40 * 3449939 * 2
def baseEnd_3449939 : Nat := 1771476935691682831496525

theorem tailTrace_3449939 : CollatzResearch.WordTrace tailWord_3449939 prefixEnd_3449939 1771476935691682831496525 := by
  unfold tailWord_3449939
  simp only [CollatzResearch.WordTrace]
  refine ⟨125829612648467680517488871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83886408432311787011659247 125829612648467680517488871)
  ·
    refine ⟨188744418972701520776233307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125829612648467680517488871 188744418972701520776233307)
    ·
      refine ⟨283116628459052281164349961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188744418972701520776233307 283116628459052281164349961)
      ·
        refine ⟨212337471344289210873262471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283116628459052281164349961 212337471344289210873262471)
        ·
          refine ⟨318506207016433816309893707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212337471344289210873262471 318506207016433816309893707)
          ·
            refine ⟨477759310524650724464840561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318506207016433816309893707 477759310524650724464840561)
            ·
              refine ⟨358319482893488043348630421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 477759310524650724464840561 358319482893488043348630421)
              ·
                refine ⟨16796225760632252031967051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 358319482893488043348630421 16796225760632252031967051)
                ·
                  refine ⟨25194338640948378047950577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16796225760632252031967051 25194338640948378047950577)
                  ·
                    refine ⟨18895753980711283535962933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25194338640948378047950577 18895753980711283535962933)
                    ·
                      refine ⟨1771476935691682831496525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18895753980711283535962933 1771476935691682831496525)
                      ·
                        rfl

theorem cell23_3449939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 5].length) (baseStart_3449939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3449939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3449939 prefixEnd_3449939 := by exact prefixLift 3449939
  have htrace : WordTrace (prefixWord ++ tailWord_3449939) baseStart_3449939 baseEnd_3449939 := by
    simpa [prefixWord, tailWord_3449939, baseEnd_3449939] using wordTrace_append hprefix tailTrace_3449939
  have hstable : (prefixWord ++ tailWord_3449939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449939).length < 2 ^ (prefixWord ++ tailWord_3449939).sum := by decide
  have hdescent : baseEnd_3449939 < baseStart_3449939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449960 : List Nat := [2, 1, 4, 4, 1, 1, 1, 1, 2, 3, 3]
def baseStart_3449960 : Nat := 118140960795 + 3449960 * 2 ^ 59
def prefixEnd_3449960 : Nat := 4983230072969 + 3 ^ 40 * 3449960 * 2
def baseEnd_3449960 : Nat := 1771487718785427249333929

theorem tailTrace_3449960 : CollatzResearch.WordTrace tailWord_3449960 prefixEnd_3449960 1771487718785427249333929 := by
  unfold tailWord_3449960
  simp only [CollatzResearch.WordTrace]
  refine ⟨62915189290695800552001667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83886919054261067402668889 62915189290695800552001667)
  ·
    refine ⟨94372783936043700828002501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62915189290695800552001667 94372783936043700828002501)
    ·
      refine ⟨17694896988008193905250469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94372783936043700828002501 17694896988008193905250469)
      ·
        refine ⟨3317793185251536357234463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17694896988008193905250469 3317793185251536357234463)
        ·
          refine ⟨4976689777877304535851695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3317793185251536357234463 4976689777877304535851695)
          ·
            refine ⟨7465034666815956803777543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4976689777877304535851695 7465034666815956803777543)
            ·
              refine ⟨11197552000223935205666315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7465034666815956803777543 11197552000223935205666315)
              ·
                refine ⟨16796328000335902808499473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11197552000223935205666315 16796328000335902808499473)
                ·
                  refine ⟨12597246000251927106374605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16796328000335902808499473 12597246000251927106374605)
                  ·
                    refine ⟨4723967250094472664890477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12597246000251927106374605 4723967250094472664890477)
                    ·
                      refine ⟨1771487718785427249333929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4723967250094472664890477 1771487718785427249333929)
                      ·
                        rfl

theorem cell23_3449960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_3449960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3449960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3449960 prefixEnd_3449960 := by exact prefixLift 3449960
  have htrace : WordTrace (prefixWord ++ tailWord_3449960) baseStart_3449960 baseEnd_3449960 := by
    simpa [prefixWord, tailWord_3449960, baseEnd_3449960] using wordTrace_append hprefix tailTrace_3449960
  have hstable : (prefixWord ++ tailWord_3449960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449960).length < 2 ^ (prefixWord ++ tailWord_3449960).sum := by decide
  have hdescent : baseEnd_3449960 < baseStart_3449960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449976 : List Nat := [2, 1, 2, 1, 1, 1, 5, 1, 5, 4]
def baseStart_3449976 : Nat := 118140960795 + 3449976 * 2 ^ 59
def prefixEnd_3449976 : Nat := 4983230072969 + 3 ^ 40 * 3449976 * 2
def baseEnd_3449976 : Nat := 590498644825299728911285

theorem tailTrace_3449976 : CollatzResearch.WordTrace tailWord_3449976 prefixEnd_3449976 590498644825299728911285 := by
  unfold tailWord_3449976
  simp only [CollatzResearch.WordTrace]
  refine ⟨62915481074666817918292891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83887308099555757224390521 62915481074666817918292891)
  ·
    refine ⟨94373221612000226877439337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62915481074666817918292891 94373221612000226877439337)
    ·
      refine ⟨70779916209000170158079503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94373221612000226877439337 70779916209000170158079503)
      ·
        refine ⟨106169874313500255237119255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70779916209000170158079503 106169874313500255237119255)
        ·
          refine ⟨159254811470250382855678883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106169874313500255237119255 159254811470250382855678883)
          ·
            refine ⟨238882217205375574283518325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159254811470250382855678883 238882217205375574283518325)
            ·
              refine ⟨22395207863003960089079843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 238882217205375574283518325 22395207863003960089079843)
              ·
                refine ⟨33592811794505940133619765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22395207863003960089079843 33592811794505940133619765)
                ·
                  refine ⟨3149326105734931887526853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33592811794505940133619765 3149326105734931887526853)
                  ·
                    refine ⟨590498644825299728911285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3149326105734931887526853 590498644825299728911285)
                    ·
                      rfl

theorem cell23_3449976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 5, 4].length) (baseStart_3449976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3449976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3449976 prefixEnd_3449976 := by exact prefixLift 3449976
  have htrace : WordTrace (prefixWord ++ tailWord_3449976) baseStart_3449976 baseEnd_3449976 := by
    simpa [prefixWord, tailWord_3449976, baseEnd_3449976] using wordTrace_append hprefix tailTrace_3449976
  have hstable : (prefixWord ++ tailWord_3449976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449976).length < 2 ^ (prefixWord ++ tailWord_3449976).sum := by decide
  have hdescent : baseEnd_3449976 < baseStart_3449976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3449979 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 6]
def baseStart_3449979 : Nat := 118140960795 + 3449979 * 2 ^ 59
def prefixEnd_3449979 : Nat := 4983230072969 + 3 ^ 40 * 3449979 * 2
def baseEnd_3449979 : Nat := 1771497474917862674996341

theorem tailTrace_3449979 : CollatzResearch.WordTrace tailWord_3449979 prefixEnd_3449979 1771497474917862674996341 := by
  unfold tailWord_3449979
  simp only [CollatzResearch.WordTrace]
  refine ⟨125831071568322767348944991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83887381045548511565963327 125831071568322767348944991)
  ·
    refine ⟨188746607352484151023417487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125831071568322767348944991 188746607352484151023417487)
    ·
      refine ⟨283119911028726226535126231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188746607352484151023417487 283119911028726226535126231)
      ·
        refine ⟨424679866543089339802689347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283119911028726226535126231 424679866543089339802689347)
        ·
          refine ⟨637019799814634009704034021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424679866543089339802689347 637019799814634009704034021)
          ·
            refine ⟨119441212465243876819506379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 637019799814634009704034021 119441212465243876819506379)
            ·
              refine ⟨179161818697865815229259569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119441212465243876819506379 179161818697865815229259569)
              ·
                refine ⟨134371364023399361421944677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179161818697865815229259569 134371364023399361421944677)
                ·
                  refine ⟨25194630754387380266614627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 134371364023399361421944677 25194630754387380266614627)
                  ·
                    refine ⟨37791946131581070399921941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25194630754387380266614627 37791946131581070399921941)
                    ·
                      refine ⟨1771497474917862674996341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37791946131581070399921941 1771497474917862674996341)
                      ·
                        rfl

theorem cell23_3449979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 6].length) (baseStart_3449979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3449979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3449979 prefixEnd_3449979 := by exact prefixLift 3449979
  have htrace : WordTrace (prefixWord ++ tailWord_3449979) baseStart_3449979 baseEnd_3449979 := by
    simpa [prefixWord, tailWord_3449979, baseEnd_3449979] using wordTrace_append hprefix tailTrace_3449979
  have hstable : (prefixWord ++ tailWord_3449979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3449979).length < 2 ^ (prefixWord ++ tailWord_3449979).sum := by decide
  have hdescent : baseEnd_3449979 < baseStart_3449979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3449979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450010 : List Nat := [3, 1, 1, 5, 1, 2, 2, 1, 3, 4]
def baseStart_3450010 : Nat := 118140960795 + 3450010 * 2 ^ 59
def prefixEnd_3450010 : Nat := 4983230072969 + 3 ^ 40 * 3450010 * 2
def baseEnd_3450010 : Nat := 590504464272717351236233

theorem tailTrace_3450010 : CollatzResearch.WordTrace tailWord_3450010 prefixEnd_3450010 590504464272717351236233 := by
  unfold tailWord_3450010
  simp only [CollatzResearch.WordTrace]
  refine ⟨31458050557802614910830871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83888134820806973095548989 31458050557802614910830871)
  ·
    refine ⟨47187075836703922366246307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31458050557802614910830871 47187075836703922366246307)
    ·
      refine ⟨70780613755055883549369461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47187075836703922366246307 70780613755055883549369461)
      ·
        refine ⟨6635682539536489082753387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70780613755055883549369461 6635682539536489082753387)
        ·
          refine ⟨9953523809304733624130081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6635682539536489082753387 9953523809304733624130081)
          ·
            refine ⟨7465142856978550218097561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9953523809304733624130081 7465142856978550218097561)
            ·
              refine ⟨5598857142733912663573171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7465142856978550218097561 5598857142733912663573171)
              ·
                refine ⟨8398285714100868995359757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5598857142733912663573171 8398285714100868995359757)
                ·
                  refine ⟨3149357142787825873259909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8398285714100868995359757 3149357142787825873259909)
                  ·
                    refine ⟨590504464272717351236233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3149357142787825873259909 590504464272717351236233)
                    ·
                      rfl

theorem cell23_3450010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 3, 4].length) (baseStart_3450010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450010 prefixEnd_3450010 := by exact prefixLift 3450010
  have htrace : WordTrace (prefixWord ++ tailWord_3450010) baseStart_3450010 baseEnd_3450010 := by
    simpa [prefixWord, tailWord_3450010, baseEnd_3450010] using wordTrace_append hprefix tailTrace_3450010
  have hstable : (prefixWord ++ tailWord_3450010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450010).length < 2 ^ (prefixWord ++ tailWord_3450010).sum := by decide
  have hdescent : baseEnd_3450010 < baseStart_3450010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450061 : List Nat := [1, 6, 2, 2, 2, 1, 1, 1, 3, 4]
def baseStart_3450061 : Nat := 118140960795 + 3450061 * 2 ^ 59
def prefixEnd_3450061 : Nat := 4983230072969 + 3 ^ 40 * 3450061 * 2
def baseEnd_3450061 : Nat := 590513193443843784723655

theorem tailTrace_3450061 : CollatzResearch.WordTrace tailWord_3450061 prefixEnd_3450061 590513193443843784723655 := by
  unfold tailWord_3450061
  simp only [CollatzResearch.WordTrace]
  refine ⟨125834062354025695353430037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83889374902683796902286691 125834062354025695353430037)
  ·
    refine ⟨5898471672844954469692033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 125834062354025695353430037 5898471672844954469692033)
    ·
      refine ⟨4423853754633715852269025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5898471672844954469692033 4423853754633715852269025)
      ·
        refine ⟨3317890315975286889201769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4423853754633715852269025 3317890315975286889201769)
        ·
          refine ⟨2488417736981465166901327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3317890315975286889201769 2488417736981465166901327)
          ·
            refine ⟨3732626605472197750351991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2488417736981465166901327 3732626605472197750351991)
            ·
              refine ⟨5598939908208296625527987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3732626605472197750351991 5598939908208296625527987)
              ·
                refine ⟨8398409862312444938291981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5598939908208296625527987 8398409862312444938291981)
                ·
                  refine ⟨3149403698367166851859493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8398409862312444938291981 3149403698367166851859493)
                  ·
                    refine ⟨590513193443843784723655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3149403698367166851859493 590513193443843784723655)
                    ·
                      rfl

theorem cell23_3450061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_3450061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450061 prefixEnd_3450061 := by exact prefixLift 3450061
  have htrace : WordTrace (prefixWord ++ tailWord_3450061) baseStart_3450061 baseEnd_3450061 := by
    simpa [prefixWord, tailWord_3450061, baseEnd_3450061] using wordTrace_append hprefix tailTrace_3450061
  have hstable : (prefixWord ++ tailWord_3450061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450061).length < 2 ^ (prefixWord ++ tailWord_3450061).sum := by decide
  have hdescent : baseEnd_3450061 < baseStart_3450061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450087 : List Nat := [1, 1, 5, 3, 2, 2, 1, 2, 1, 5]
def baseStart_3450087 : Nat := 118140960795 + 3450087 * 2 ^ 59
def prefixEnd_3450087 : Nat := 4983230072969 + 3 ^ 40 * 3450087 * 2
def baseEnd_3450087 : Nat := 590517643609516084148615

theorem tailTrace_3450087 : CollatzResearch.WordTrace tailWord_3450087 prefixEnd_3450087 590517643609516084148615 := by
  unfold tailWord_3450087
  simp only [CollatzResearch.WordTrace]
  refine ⟨125835010651931501793876515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83890007101287667862584343 125835010651931501793876515)
  ·
    refine ⟨188752515977897252690814773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125835010651931501793876515 188752515977897252690814773)
    ·
      refine ⟨17695548372927867439763885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 188752515977897252690814773 17695548372927867439763885)
      ·
        refine ⟨6635830639847950289911457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17695548372927867439763885 6635830639847950289911457)
        ·
          refine ⟨4976872979885962717433593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6635830639847950289911457 4976872979885962717433593)
          ·
            refine ⟨3732654734914472038075195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4976872979885962717433593 3732654734914472038075195)
            ·
              refine ⟨5598982102371708057112793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3732654734914472038075195 5598982102371708057112793)
              ·
                refine ⟨4199236576778781042834595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5598982102371708057112793 4199236576778781042834595)
                ·
                  refine ⟨6298854865168171564251893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4199236576778781042834595 6298854865168171564251893)
                  ·
                    refine ⟨590517643609516084148615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6298854865168171564251893 590517643609516084148615)
                    ·
                      rfl

theorem cell23_3450087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_3450087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450087 prefixEnd_3450087 := by exact prefixLift 3450087
  have htrace : WordTrace (prefixWord ++ tailWord_3450087) baseStart_3450087 baseEnd_3450087 := by
    simpa [prefixWord, tailWord_3450087, baseEnd_3450087] using wordTrace_append hprefix tailTrace_3450087
  have hstable : (prefixWord ++ tailWord_3450087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450087).length < 2 ^ (prefixWord ++ tailWord_3450087).sum := by decide
  have hdescent : baseEnd_3450087 < baseStart_3450087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450090 : List Nat := [3, 1, 3, 1, 1, 3, 3, 2, 1, 1, 4]
def baseStart_3450090 : Nat := 118140960795 + 3450090 * 2 ^ 59
def prefixEnd_3450090 : Nat := 4983230072969 + 3 ^ 40 * 3450090 * 2
def baseEnd_3450090 : Nat := 1771554471270511740708331

theorem tailTrace_3450090 : CollatzResearch.WordTrace tailWord_3450090 prefixEnd_3450090 1771554471270511740708331 := by
  unfold tailWord_3450090
  simp only [CollatzResearch.WordTrace]
  refine ⟨31458780017730158326558931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83890080047280422204157149 31458780017730158326558931)
  ·
    refine ⟨47188170026595237489838397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31458780017730158326558931 47188170026595237489838397)
    ·
      refine ⟨17695563759973214058689399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47188170026595237489838397 17695563759973214058689399)
      ·
        refine ⟨26543345639959821088034099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17695563759973214058689399 26543345639959821088034099)
        ·
          refine ⟨39815018459939731632051149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26543345639959821088034099 39815018459939731632051149)
          ·
            refine ⟨14930631922477399362019181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39815018459939731632051149 14930631922477399362019181)
            ·
              refine ⟨5598986970929024760757193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14930631922477399362019181 5598986970929024760757193)
              ·
                refine ⟨4199240228196768570567895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5598986970929024760757193 4199240228196768570567895)
                ·
                  refine ⟨6298860342295152855851843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4199240228196768570567895 6298860342295152855851843)
                  ·
                    refine ⟨9448290513442729283777765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6298860342295152855851843 9448290513442729283777765)
                    ·
                      refine ⟨1771554471270511740708331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9448290513442729283777765 1771554471270511740708331)
                      ·
                        rfl

theorem cell23_3450090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_3450090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450090 prefixEnd_3450090 := by exact prefixLift 3450090
  have htrace : WordTrace (prefixWord ++ tailWord_3450090) baseStart_3450090 baseEnd_3450090 := by
    simpa [prefixWord, tailWord_3450090, baseEnd_3450090] using wordTrace_append hprefix tailTrace_3450090
  have hstable : (prefixWord ++ tailWord_3450090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450090).length < 2 ^ (prefixWord ++ tailWord_3450090).sum := by decide
  have hdescent : baseEnd_3450090 < baseStart_3450090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450110 : List Nat := [4, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5]
def baseStart_3450110 : Nat := 118140960795 + 3450110 * 2 ^ 59
def prefixEnd_3450110 : Nat := 4983230072969 + 3 ^ 40 * 3450110 * 2
def baseEnd_3450110 : Nat := 1771564740883601662458239

theorem tailTrace_3450110 : CollatzResearch.WordTrace tailWord_3450110 prefixEnd_3450110 1771564740883601662458239 := by
  unfold tailWord_3450110
  simp only [CollatzResearch.WordTrace]
  refine ⟨15729481191356022090245473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83890566353898784481309189 15729481191356022090245473)
  ·
    refine ⟨11797110893517016567684105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15729481191356022090245473 11797110893517016567684105)
    ·
      refine ⟨8847833170137762425763079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11797110893517016567684105 8847833170137762425763079)
      ·
        refine ⟨13271749755206643638644619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8847833170137762425763079 13271749755206643638644619)
        ·
          refine ⟨19907624632809965457966929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13271749755206643638644619 19907624632809965457966929)
          ·
            refine ⟨14930718474607474093475197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19907624632809965457966929 14930718474607474093475197)
            ·
              refine ⟨5599019427977802785053199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14930718474607474093475197 5599019427977802785053199)
              ·
                refine ⟨8398529141966704177579799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5599019427977802785053199 8398529141966704177579799)
                ·
                  refine ⟨12597793712950056266369699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8398529141966704177579799 12597793712950056266369699)
                  ·
                    refine ⟨18896690569425084399554549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12597793712950056266369699 18896690569425084399554549)
                    ·
                      refine ⟨1771564740883601662458239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18896690569425084399554549 1771564740883601662458239)
                      ·
                        rfl

theorem cell23_3450110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_3450110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450110 prefixEnd_3450110 := by exact prefixLift 3450110
  have htrace : WordTrace (prefixWord ++ tailWord_3450110) baseStart_3450110 baseEnd_3450110 := by
    simpa [prefixWord, tailWord_3450110, baseEnd_3450110] using wordTrace_append hprefix tailTrace_3450110
  have hstable : (prefixWord ++ tailWord_3450110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450110).length < 2 ^ (prefixWord ++ tailWord_3450110).sum := by decide
  have hdescent : baseEnd_3450110 < baseStart_3450110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450124 : List Nat := [2, 2, 1, 2, 2, 4, 1, 4, 1, 2, 2]
def baseStart_3450124 : Nat := 118140960795 + 3450124 * 2 ^ 59
def prefixEnd_3450124 : Nat := 4983230072969 + 3 ^ 40 * 3450124 * 2
def baseEnd_3450124 : Nat := 1771571929612764607683175

theorem tailTrace_3450124 : CollatzResearch.WordTrace tailWord_3450124 prefixEnd_3450124 1771571929612764607683175 := by
  unfold tailWord_3450124
  simp only [CollatzResearch.WordTrace]
  refine ⟨62918180076398728556486713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83890906768531638075315617 62918180076398728556486713)
  ·
    refine ⟨47188635057299046417365035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62918180076398728556486713 47188635057299046417365035)
    ·
      refine ⟨70782952585948569626047553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47188635057299046417365035 70782952585948569626047553)
      ·
        refine ⟨53087214439461427219535665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70782952585948569626047553 53087214439461427219535665)
        ·
          refine ⟨39815410829596070414651749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53087214439461427219535665 39815410829596070414651749)
          ·
            refine ⟨7465389530549263202747203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39815410829596070414651749 7465389530549263202747203)
            ·
              refine ⟨11198084295823894804120805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7465389530549263202747203 11198084295823894804120805)
              ·
                refine ⟨2099640805466980275772651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11198084295823894804120805 2099640805466980275772651)
                ·
                  refine ⟨3149461208200470413658977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2099640805466980275772651 3149461208200470413658977)
                  ·
                    refine ⟨2362095906150352810244233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3149461208200470413658977 2362095906150352810244233)
                    ·
                      refine ⟨1771571929612764607683175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2362095906150352810244233 1771571929612764607683175)
                      ·
                        rfl

theorem cell23_3450124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 4, 1, 2, 2].length) (baseStart_3450124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450124 prefixEnd_3450124 := by exact prefixLift 3450124
  have htrace : WordTrace (prefixWord ++ tailWord_3450124) baseStart_3450124 baseEnd_3450124 := by
    simpa [prefixWord, tailWord_3450124, baseEnd_3450124] using wordTrace_append hprefix tailTrace_3450124
  have hstable : (prefixWord ++ tailWord_3450124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450124).length < 2 ^ (prefixWord ++ tailWord_3450124).sum := by decide
  have hdescent : baseEnd_3450124 < baseStart_3450124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450156 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 3, 8]
def baseStart_3450156 : Nat := 118140960795 + 3450156 * 2 ^ 59
def prefixEnd_3450156 : Nat := 4983230072969 + 3 ^ 40 * 3450156 * 2
def baseEnd_3450156 : Nat := 590529453664569494161009

theorem tailTrace_3450156 : CollatzResearch.WordTrace tailWord_3450156 prefixEnd_3450156 590529453664569494161009 := by
  unfold tailWord_3450156
  simp only [CollatzResearch.WordTrace]
  refine ⟨62918763644340763289069161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83891684859121017718758881 62918763644340763289069161)
  ·
    refine ⟨47189072733255572466801871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62918763644340763289069161 47189072733255572466801871)
    ·
      refine ⟨70783609099883358700202807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47189072733255572466801871 70783609099883358700202807)
      ·
        refine ⟨106175413649825038050304211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70783609099883358700202807 106175413649825038050304211)
        ·
          refine ⟨159263120474737557075456317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106175413649825038050304211 159263120474737557075456317)
          ·
            refine ⟨59723670178026583903296119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159263120474737557075456317 59723670178026583903296119)
            ·
              refine ⟨89585505267039875854944179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59723670178026583903296119 89585505267039875854944179)
              ·
                refine ⟨134378257900559813782416269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89585505267039875854944179 134378257900559813782416269)
                ·
                  refine ⟨50391846712709930168406101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134378257900559813782416269 50391846712709930168406101)
                  ·
                    refine ⟨590529453664569494161009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 50391846712709930168406101 590529453664569494161009)
                    ·
                      rfl

theorem cell23_3450156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 8].length) (baseStart_3450156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450156 prefixEnd_3450156 := by exact prefixLift 3450156
  have htrace : WordTrace (prefixWord ++ tailWord_3450156) baseStart_3450156 baseEnd_3450156 := by
    simpa [prefixWord, tailWord_3450156, baseEnd_3450156] using wordTrace_append hprefix tailTrace_3450156
  have hstable : (prefixWord ++ tailWord_3450156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450156).length < 2 ^ (prefixWord ++ tailWord_3450156).sum := by decide
  have hdescent : baseEnd_3450156 < baseStart_3450156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450157 : List Nat := [1, 5, 3, 1, 1, 1, 2, 2, 1, 3, 3]
def baseStart_3450157 : Nat := 118140960795 + 3450157 * 2 ^ 59
def prefixEnd_3450157 : Nat := 4983230072969 + 3 ^ 40 * 3450157 * 2
def baseEnd_3450157 : Nat := 1771588874474362978570523

theorem tailTrace_3450157 : CollatzResearch.WordTrace tailWord_3450157 prefixEnd_3450157 1771588874474362978570523 := by
  unfold tailWord_3450157
  simp only [CollatzResearch.WordTrace]
  refine ⟨125837563761677903748924725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83891709174451935832616483 125837563761677903748924725)
  ·
    refine ⟨11797271602657303476461693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125837563761677903748924725 11797271602657303476461693)
    ·
      refine ⟨4423976850996488803673135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11797271602657303476461693 4423976850996488803673135)
      ·
        refine ⟨6635965276494733205509703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4423976850996488803673135 6635965276494733205509703)
        ·
          refine ⟨9953947914742099808264555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6635965276494733205509703 9953947914742099808264555)
          ·
            refine ⟨14930921872113149712396833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9953947914742099808264555 14930921872113149712396833)
            ·
              refine ⟨11198191404084862284297625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14930921872113149712396833 11198191404084862284297625)
              ·
                refine ⟨8398643553063646713223219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11198191404084862284297625 8398643553063646713223219)
                ·
                  refine ⟨12597965329595470069834829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8398643553063646713223219 12597965329595470069834829)
                  ·
                    refine ⟨4724236998598301276188061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12597965329595470069834829 4724236998598301276188061)
                    ·
                      refine ⟨1771588874474362978570523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4724236998598301276188061 1771588874474362978570523)
                      ·
                        rfl

theorem cell23_3450157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_3450157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450157 prefixEnd_3450157 := by exact prefixLift 3450157
  have htrace : WordTrace (prefixWord ++ tailWord_3450157) baseStart_3450157 baseEnd_3450157 := by
    simpa [prefixWord, tailWord_3450157, baseEnd_3450157] using wordTrace_append hprefix tailTrace_3450157
  have hstable : (prefixWord ++ tailWord_3450157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450157).length < 2 ^ (prefixWord ++ tailWord_3450157).sum := by decide
  have hdescent : baseEnd_3450157 < baseStart_3450157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450193 : List Nat := [1, 2, 2, 1, 4, 1, 1, 3, 2, 2, 4]
def baseStart_3450193 : Nat := 118140960795 + 3450193 * 2 ^ 59
def prefixEnd_3450193 : Nat := 4983230072969 + 3 ^ 40 * 3450193 * 2
def baseEnd_3450193 : Nat := 1771607359777924837720357

theorem tailTrace_3450193 : CollatzResearch.WordTrace tailWord_3450193 prefixEnd_3450193 1771607359777924837720357 := by
  unfold tailWord_3450193
  simp only [CollatzResearch.WordTrace]
  refine ⟨125838876789547481897235233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83892584526364987931490155 125838876789547481897235233)
  ·
    refine ⟨94379157592160611422926425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125838876789547481897235233 94379157592160611422926425)
    ·
      refine ⟨70784368194120458567194819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94379157592160611422926425 70784368194120458567194819)
      ·
        refine ⟨106176552291180687850792229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70784368194120458567194819 106176552291180687850792229)
        ·
          refine ⟨19908103554596378972023543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106176552291180687850792229 19908103554596378972023543)
          ·
            refine ⟨29862155331894568458035315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19908103554596378972023543 29862155331894568458035315)
            ·
              refine ⟨44793232997841852687052973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29862155331894568458035315 44793232997841852687052973)
              ·
                refine ⟨16797462374190694757644865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44793232997841852687052973 16797462374190694757644865)
                ·
                  refine ⟨12598096780643021068233649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16797462374190694757644865 12598096780643021068233649)
                  ·
                    refine ⟨9448572585482265801175237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12598096780643021068233649 9448572585482265801175237)
                    ·
                      refine ⟨1771607359777924837720357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9448572585482265801175237 1771607359777924837720357)
                      ·
                        rfl

theorem cell23_3450193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 2, 4].length) (baseStart_3450193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450193 prefixEnd_3450193 := by exact prefixLift 3450193
  have htrace : WordTrace (prefixWord ++ tailWord_3450193) baseStart_3450193 baseEnd_3450193 := by
    simpa [prefixWord, tailWord_3450193, baseEnd_3450193] using wordTrace_append hprefix tailTrace_3450193
  have hstable : (prefixWord ++ tailWord_3450193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450193).length < 2 ^ (prefixWord ++ tailWord_3450193).sum := by decide
  have hdescent : baseEnd_3450193 < baseStart_3450193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450197 : List Nat := [1, 3, 2, 2, 3, 1, 3, 1, 1, 4, 2]
def baseStart_3450197 : Nat := 118140960795 + 3450197 * 2 ^ 59
def prefixEnd_3450197 : Nat := 4983230072969 + 3 ^ 40 * 3450197 * 2
def baseEnd_3450197 : Nat := 1771609413700542822070339

theorem tailTrace_3450197 : CollatzResearch.WordTrace tailWord_3450197 prefixEnd_3450197 1771609413700542822070339 := by
  unfold tailWord_3450197
  simp only [CollatzResearch.WordTrace]
  refine ⟨125839022681532990580380845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83892681787688660386920563 125839022681532990580380845)
  ·
    refine ⟨47189633505574871467642817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125839022681532990580380845 47189633505574871467642817)
    ·
      refine ⟨35392225129181153600732113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47189633505574871467642817 35392225129181153600732113)
      ·
        refine ⟨26544168846885865200549085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35392225129181153600732113 26544168846885865200549085)
        ·
          refine ⟨9954063317582199450205907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26544168846885865200549085 9954063317582199450205907)
          ·
            refine ⟨14931094976373299175308861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9954063317582199450205907 14931094976373299175308861)
            ·
              refine ⟨5599160616139987190740823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14931094976373299175308861 5599160616139987190740823)
              ·
                refine ⟨8398740924209980786111235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5599160616139987190740823 8398740924209980786111235)
                ·
                  refine ⟨12598111386314971179166853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8398740924209980786111235 12598111386314971179166853)
                  ·
                    refine ⟨2362145884934057096093785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12598111386314971179166853 2362145884934057096093785)
                    ·
                      refine ⟨1771609413700542822070339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2362145884934057096093785 1771609413700542822070339)
                      ·
                        rfl

theorem cell23_3450197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 4, 2].length) (baseStart_3450197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450197 prefixEnd_3450197 := by exact prefixLift 3450197
  have htrace : WordTrace (prefixWord ++ tailWord_3450197) baseStart_3450197 baseEnd_3450197 := by
    simpa [prefixWord, tailWord_3450197, baseEnd_3450197] using wordTrace_append hprefix tailTrace_3450197
  have hstable : (prefixWord ++ tailWord_3450197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450197).length < 2 ^ (prefixWord ++ tailWord_3450197).sum := by decide
  have hdescent : baseEnd_3450197 < baseStart_3450197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450198 : List Nat := [5, 2, 3, 1, 2, 1, 2, 7]
def baseStart_3450198 : Nat := 118140960795 + 3450198 * 2 ^ 59
def prefixEnd_3450198 : Nat := 4983230072969 + 3 ^ 40 * 3450198 * 2
def baseEnd_3450198 : Nat := 65615182488192493265105

theorem tailTrace_3450198 : CollatzResearch.WordTrace tailWord_3450198 prefixEnd_3450198 65615182488192493265105 := by
  unfold tailWord_3450198
  simp only [CollatzResearch.WordTrace]
  refine ⟨7864941197158085484447953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83892706103019578500778165 7864941197158085484447953)
  ·
    refine ⟨5898705897868564113335965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7864941197158085484447953 5898705897868564113335965)
    ·
      refine ⟨2212014711700711542500987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5898705897868564113335965 2212014711700711542500987)
      ·
        refine ⟨3318022067551067313751481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2212014711700711542500987 3318022067551067313751481)
        ·
          refine ⟨2488516550663300485313611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3318022067551067313751481 2488516550663300485313611)
          ·
            refine ⟨3732774825994950727970417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2488516550663300485313611 3732774825994950727970417)
            ·
              refine ⟨2799581119496213045977813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3732774825994950727970417 2799581119496213045977813)
              ·
                refine ⟨65615182488192493265105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2799581119496213045977813 65615182488192493265105)
                ·
                  rfl

theorem cell23_3450198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 7].length) (baseStart_3450198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450198 prefixEnd_3450198 := by exact prefixLift 3450198
  have htrace : WordTrace (prefixWord ++ tailWord_3450198) baseStart_3450198 baseEnd_3450198 := by
    simpa [prefixWord, tailWord_3450198, baseEnd_3450198] using wordTrace_append hprefix tailTrace_3450198
  have hstable : (prefixWord ++ tailWord_3450198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450198).length < 2 ^ (prefixWord ++ tailWord_3450198).sum := by decide
  have hdescent : baseEnd_3450198 < baseStart_3450198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450233 : List Nat := [1, 2, 1, 3, 2, 1, 3, 1, 4, 5]
def baseStart_3450233 : Nat := 118140960795 + 3450233 * 2 ^ 59
def prefixEnd_3450233 : Nat := 4983230072969 + 3 ^ 40 * 3450233 * 2
def baseEnd_3450233 : Nat := 590542633001368227073391

theorem tailTrace_3450233 : CollatzResearch.WordTrace tailWord_3450233 prefixEnd_3450233 590542633001368227073391 := by
  unfold tailWord_3450233
  simp only [CollatzResearch.WordTrace]
  refine ⟨125840335709402568728691353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83893557139601712485794235 125840335709402568728691353)
  ·
    refine ⟨94380251782051926546518515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125840335709402568728691353 94380251782051926546518515)
    ·
      refine ⟨141570377673077889819777773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94380251782051926546518515 141570377673077889819777773)
      ·
        refine ⟨53088891627404208682416665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141570377673077889819777773 53088891627404208682416665)
        ·
          refine ⟨39816668720553156511812499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53088891627404208682416665 39816668720553156511812499)
          ·
            refine ⟨59725003080829734767718749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39816668720553156511812499 59725003080829734767718749)
            ·
              refine ⟨22396876155311150537894531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59725003080829734767718749 22396876155311150537894531)
              ·
                refine ⟨33595314232966725806841797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22396876155311150537894531 33595314232966725806841797)
                ·
                  refine ⟨6299121418681261088782837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33595314232966725806841797 6299121418681261088782837)
                  ·
                    refine ⟨590542633001368227073391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6299121418681261088782837 590542633001368227073391)
                    ·
                      rfl

theorem cell23_3450233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 4, 5].length) (baseStart_3450233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450233 prefixEnd_3450233 := by exact prefixLift 3450233
  have htrace : WordTrace (prefixWord ++ tailWord_3450233) baseStart_3450233 baseEnd_3450233 := by
    simpa [prefixWord, tailWord_3450233, baseEnd_3450233] using wordTrace_append hprefix tailTrace_3450233
  have hstable : (prefixWord ++ tailWord_3450233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450233).length < 2 ^ (prefixWord ++ tailWord_3450233).sum := by decide
  have hdescent : baseEnd_3450233 < baseStart_3450233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450237 : List Nat := [1, 4, 1, 1, 2, 2, 5, 2, 5]
def baseStart_3450237 : Nat := 118140960795 + 3450237 * 2 ^ 59
def prefixEnd_3450237 : Nat := 4983230072969 + 3 ^ 40 * 3450237 * 2
def baseEnd_3450237 : Nat := 196847772547413629507795

theorem tailTrace_3450237 : CollatzResearch.WordTrace tailWord_3450237 prefixEnd_3450237 196847772547413629507795 := by
  unfold tailWord_3450237
  simp only [CollatzResearch.WordTrace]
  refine ⟨125840481601388077411836965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83893654400925384941224643 125840481601388077411836965)
  ·
    refine ⟨23595090300260264514719431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125840481601388077411836965 23595090300260264514719431)
    ·
      refine ⟨35392635450390396772079147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23595090300260264514719431 35392635450390396772079147)
      ·
        refine ⟨53088953175585595158118721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35392635450390396772079147 53088953175585595158118721)
        ·
          refine ⟨39816714881689196368589041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53088953175585595158118721 39816714881689196368589041)
          ·
            refine ⟨29862536161266897276441781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39816714881689196368589041 29862536161266897276441781)
            ·
              refine ⟨2799612765118771619666417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29862536161266897276441781 2799612765118771619666417)
              ·
                refine ⟨2099709573839078714749813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2799612765118771619666417 2099709573839078714749813)
                ·
                  refine ⟨196847772547413629507795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2099709573839078714749813 196847772547413629507795)
                  ·
                    rfl

theorem cell23_3450237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 2, 5].length) (baseStart_3450237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450237 prefixEnd_3450237 := by exact prefixLift 3450237
  have htrace : WordTrace (prefixWord ++ tailWord_3450237) baseStart_3450237 baseEnd_3450237 := by
    simpa [prefixWord, tailWord_3450237, baseEnd_3450237] using wordTrace_append hprefix tailTrace_3450237
  have hstable : (prefixWord ++ tailWord_3450237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450237).length < 2 ^ (prefixWord ++ tailWord_3450237).sum := by decide
  have hdescent : baseEnd_3450237 < baseStart_3450237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450243 : List Nat := [1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 7]
def baseStart_3450243 : Nat := 118140960795 + 3450243 * 2 ^ 59
def prefixEnd_3450243 : Nat := 4983230072969 + 3 ^ 40 * 3450243 * 2
def baseEnd_3450243 : Nat := 1771633033810649642095127

theorem tailTrace_3450243 : CollatzResearch.WordTrace tailWord_3450243 prefixEnd_3450243 1771633033810649642095127 := by
  unfold tailWord_3450243
  simp only [CollatzResearch.WordTrace]
  refine ⟨125840700439366340436555383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83893800292910893624370255 125840700439366340436555383)
  ·
    refine ⟨188761050659049510654833075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125840700439366340436555383 188761050659049510654833075)
    ·
      refine ⟨283141575988574265982249613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188761050659049510654833075 283141575988574265982249613)
      ·
        refine ⟨106178090995715349743343605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 283141575988574265982249613 106178090995715349743343605)
        ·
          refine ⟨9954196030848314038438463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106178090995715349743343605 9954196030848314038438463)
          ·
            refine ⟨14931294046272471057657695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9954196030848314038438463 14931294046272471057657695)
            ·
              refine ⟨22396941069408706586486543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14931294046272471057657695 22396941069408706586486543)
              ·
                refine ⟨33595411604113059879729815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22396941069408706586486543 33595411604113059879729815)
                ·
                  refine ⟨50393117406169589819594723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33595411604113059879729815 50393117406169589819594723)
                  ·
                    refine ⟨75589676109254384729392085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50393117406169589819594723 75589676109254384729392085)
                    ·
                      refine ⟨1771633033810649642095127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 75589676109254384729392085 1771633033810649642095127)
                      ·
                        rfl

theorem cell23_3450243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 7].length) (baseStart_3450243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450243 prefixEnd_3450243 := by exact prefixLift 3450243
  have htrace : WordTrace (prefixWord ++ tailWord_3450243) baseStart_3450243 baseEnd_3450243 := by
    simpa [prefixWord, tailWord_3450243, baseEnd_3450243] using wordTrace_append hprefix tailTrace_3450243
  have hstable : (prefixWord ++ tailWord_3450243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450243).length < 2 ^ (prefixWord ++ tailWord_3450243).sum := by decide
  have hdescent : baseEnd_3450243 < baseStart_3450243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450290 : List Nat := [3, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3]
def baseStart_3450290 : Nat := 118140960795 + 3450290 * 2 ^ 59
def prefixEnd_3450290 : Nat := 4983230072969 + 3 ^ 40 * 3450290 * 2
def baseEnd_3450290 : Nat := 1771657167401410958207411

theorem tailTrace_3450290 : CollatzResearch.WordTrace tailWord_3450290 prefixEnd_3450290 1771657167401410958207411 := by
  unfold tailWord_3450290
  simp only [CollatzResearch.WordTrace]
  refine ⟨31460603667549016865879081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83894943113464044975677549 31460603667549016865879081)
  ·
    refine ⟨23595452750661762649409311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31460603667549016865879081 23595452750661762649409311)
    ·
      refine ⟨35393179125992643974113967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23595452750661762649409311 35393179125992643974113967)
      ·
        refine ⟨53089768688988965961170951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35393179125992643974113967 53089768688988965961170951)
        ·
          refine ⟨79634653033483448941756427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53089768688988965961170951 79634653033483448941756427)
          ·
            refine ⟨119451979550225173412634641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79634653033483448941756427 119451979550225173412634641)
            ·
              refine ⟨89588984662668880059475981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119451979550225173412634641 89588984662668880059475981)
              ·
                refine ⟨33595869248500830022303493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89588984662668880059475981 33595869248500830022303493)
                ·
                  refine ⟨6299225484093905629181905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33595869248500830022303493 6299225484093905629181905)
                  ·
                    refine ⟨4724419113070429221886429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6299225484093905629181905 4724419113070429221886429)
                    ·
                      refine ⟨1771657167401410958207411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4724419113070429221886429 1771657167401410958207411)
                      ·
                        rfl

theorem cell23_3450290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3].length) (baseStart_3450290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450290 prefixEnd_3450290 := by exact prefixLift 3450290
  have htrace : WordTrace (prefixWord ++ tailWord_3450290) baseStart_3450290 baseEnd_3450290 := by
    simpa [prefixWord, tailWord_3450290, baseEnd_3450290] using wordTrace_append hprefix tailTrace_3450290
  have hstable : (prefixWord ++ tailWord_3450290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450290).length < 2 ^ (prefixWord ++ tailWord_3450290).sum := by decide
  have hdescent : baseEnd_3450290 < baseStart_3450290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450354 : List Nat := [3, 2, 1, 4, 1, 1, 1, 3, 3, 1, 3]
def baseStart_3450354 : Nat := 118140960795 + 3450354 * 2 ^ 59
def prefixEnd_3450354 : Nat := 4983230072969 + 3 ^ 40 * 3450354 * 2
def baseEnd_3450354 : Nat := 1771690030163298707807117

theorem tailTrace_3450354 : CollatzResearch.WordTrace tailWord_3450354 prefixEnd_3450354 1771690030163298707807117 := by
  unfold tailWord_3450354
  simp only [CollatzResearch.WordTrace]
  refine ⟨31461187235491051598461529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83896499294642804262564077 31461187235491051598461529)
  ·
    refine ⟨23595890426618288698846147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31461187235491051598461529 23595890426618288698846147)
    ·
      refine ⟨35393835639927433048269221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23595890426618288698846147 35393835639927433048269221)
      ·
        refine ⟨6636344182486393696550479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35393835639927433048269221 6636344182486393696550479)
        ·
          refine ⟨9954516273729590544825719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6636344182486393696550479 9954516273729590544825719)
          ·
            refine ⟨14931774410594385817238579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9954516273729590544825719 14931774410594385817238579)
            ·
              refine ⟨22397661615891578725857869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14931774410594385817238579 22397661615891578725857869)
              ·
                refine ⟨8399123105959342022196701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22397661615891578725857869 8399123105959342022196701)
                ·
                  refine ⟨3149671164734753258323763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8399123105959342022196701 3149671164734753258323763)
                  ·
                    refine ⟨4724506747102129887485645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3149671164734753258323763 4724506747102129887485645)
                    ·
                      refine ⟨1771690030163298707807117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4724506747102129887485645 1771690030163298707807117)
                      ·
                        rfl

theorem cell23_3450354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_3450354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450354 prefixEnd_3450354 := by exact prefixLift 3450354
  have htrace : WordTrace (prefixWord ++ tailWord_3450354) baseStart_3450354 baseEnd_3450354 := by
    simpa [prefixWord, tailWord_3450354, baseEnd_3450354] using wordTrace_append hprefix tailTrace_3450354
  have hstable : (prefixWord ++ tailWord_3450354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450354).length < 2 ^ (prefixWord ++ tailWord_3450354).sum := by decide
  have hdescent : baseEnd_3450354 < baseStart_3450354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450377 : List Nat := [1, 2, 1, 1, 3, 1, 6, 2, 1, 1, 4]
def baseStart_3450377 : Nat := 118140960795 + 3450377 * 2 ^ 59
def prefixEnd_3450377 : Nat := 4983230072969 + 3 ^ 40 * 3450377 * 2
def baseEnd_3450377 : Nat := 1771701840218352117819511

theorem tailTrace_3450377 : CollatzResearch.WordTrace tailWord_3450377 prefixEnd_3450377 1771701840218352117819511 := by
  unfold tailWord_3450377
  simp only [CollatzResearch.WordTrace]
  refine ⟨125845587820880881321933385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83897058547253920881288923 125845587820880881321933385)
  ·
    refine ⟨94384190865660660991450039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125845587820880881321933385 94384190865660660991450039)
    ·
      refine ⟨141576286298490991487175059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94384190865660660991450039 141576286298490991487175059)
      ·
        refine ⟨212364429447736487230762589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141576286298490991487175059 212364429447736487230762589)
        ·
          refine ⟨79636661042901182711535971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212364429447736487230762589 79636661042901182711535971)
          ·
            refine ⟨119454991564351774067303957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79636661042901182711535971 119454991564351774067303957)
            ·
              refine ⟨5599452729578989409404873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 119454991564351774067303957 5599452729578989409404873)
              ·
                refine ⟨4199589547184242057053655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5599452729578989409404873 4199589547184242057053655)
                ·
                  refine ⟨6299384320776363085580483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4199589547184242057053655 6299384320776363085580483)
                  ·
                    refine ⟨9449076481164544628370725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6299384320776363085580483 9449076481164544628370725)
                    ·
                      refine ⟨1771701840218352117819511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9449076481164544628370725 1771701840218352117819511)
                      ·
                        rfl

theorem cell23_3450377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 2, 1, 1, 4].length) (baseStart_3450377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450377 prefixEnd_3450377 := by exact prefixLift 3450377
  have htrace : WordTrace (prefixWord ++ tailWord_3450377) baseStart_3450377 baseEnd_3450377 := by
    simpa [prefixWord, tailWord_3450377, baseEnd_3450377] using wordTrace_append hprefix tailTrace_3450377
  have hstable : (prefixWord ++ tailWord_3450377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450377).length < 2 ^ (prefixWord ++ tailWord_3450377).sum := by decide
  have hdescent : baseEnd_3450377 < baseStart_3450377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450397 : List Nat := [1, 4, 2, 2, 1, 1, 4, 1, 1, 1, 5]
def baseStart_3450397 : Nat := 118140960795 + 3450397 * 2 ^ 59
def prefixEnd_3450397 : Nat := 4983230072969 + 3 ^ 40 * 3450397 * 2
def baseEnd_3450397 : Nat := 1771712109831442039569419

theorem tailTrace_3450397 : CollatzResearch.WordTrace tailWord_3450397 prefixEnd_3450397 1771712109831442039569419 := by
  unfold tailWord_3450397
  simp only [CollatzResearch.WordTrace]
  refine ⟨125846317280808424737661445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83897544853872283158440963 125846317280808424737661445)
  ·
    refine ⟨23596184490151579638311521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125846317280808424737661445 23596184490151579638311521)
    ·
      refine ⟨17697138367613684728733641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23596184490151579638311521 17697138367613684728733641)
      ·
        refine ⟨13272853775710263546550231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17697138367613684728733641 13272853775710263546550231)
        ·
          refine ⟨19909280663565395319825347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13272853775710263546550231 19909280663565395319825347)
          ·
            refine ⟨29863920995348092979738021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19909280663565395319825347 29863920995348092979738021)
            ·
              refine ⟨5599485186627767433700879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29863920995348092979738021 5599485186627767433700879)
              ·
                refine ⟨8399227779941651150551319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5599485186627767433700879 8399227779941651150551319)
                ·
                  refine ⟨12598841669912476725826979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8399227779941651150551319 12598841669912476725826979)
                  ·
                    refine ⟨18898262504868715088740469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12598841669912476725826979 18898262504868715088740469)
                    ·
                      refine ⟨1771712109831442039569419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18898262504868715088740469 1771712109831442039569419)
                      ·
                        rfl

theorem cell23_3450397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_3450397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450397 prefixEnd_3450397 := by exact prefixLift 3450397
  have htrace : WordTrace (prefixWord ++ tailWord_3450397) baseStart_3450397 baseEnd_3450397 := by
    simpa [prefixWord, tailWord_3450397, baseEnd_3450397] using wordTrace_append hprefix tailTrace_3450397
  have hstable : (prefixWord ++ tailWord_3450397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450397).length < 2 ^ (prefixWord ++ tailWord_3450397).sum := by decide
  have hdescent : baseEnd_3450397 < baseStart_3450397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450400 : List Nat := [2, 1, 1, 6, 1, 1, 11]
def baseStart_3450400 : Nat := 118140960795 + 3450400 * 2 ^ 59
def prefixEnd_3450400 : Nat := 4983230072969 + 3 ^ 40 * 3450400 * 2
def baseEnd_3450400 : Nat := 21873008028066734911505

theorem tailTrace_3450400 : CollatzResearch.WordTrace tailWord_3450400 prefixEnd_3450400 21873008028066734911505 := by
  unfold tailWord_3450400
  simp only [CollatzResearch.WordTrace]
  refine ⟨62923213349898778125010327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83897617799865037500013769 62923213349898778125010327)
  ·
    refine ⟨94384820024848167187515491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62923213349898778125010327 94384820024848167187515491)
    ·
      refine ⟨141577230037272250781273237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94384820024848167187515491 141577230037272250781273237)
      ·
        refine ⟨6636432657997136755372183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 141577230037272250781273237 6636432657997136755372183)
        ·
          refine ⟨9954648986995705133058275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6636432657997136755372183 9954648986995705133058275)
          ·
            refine ⟨14931973480493557699587413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9954648986995705133058275 14931973480493557699587413)
            ·
              refine ⟨21873008028066734911505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 14931973480493557699587413 21873008028066734911505)
              ·
                rfl

theorem cell23_3450400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 11].length) (baseStart_3450400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450400 prefixEnd_3450400 := by exact prefixLift 3450400
  have htrace : WordTrace (prefixWord ++ tailWord_3450400) baseStart_3450400 baseEnd_3450400 := by
    simpa [prefixWord, tailWord_3450400, baseEnd_3450400] using wordTrace_append hprefix tailTrace_3450400
  have hstable : (prefixWord ++ tailWord_3450400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450400).length < 2 ^ (prefixWord ++ tailWord_3450400).sum := by decide
  have hdescent : baseEnd_3450400 < baseStart_3450400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450421 : List Nat := [1, 3, 3, 1, 1, 5, 2, 1, 2, 4]
def baseStart_3450421 : Nat := 118140960795 + 3450421 * 2 ^ 59
def prefixEnd_3450421 : Nat := 4983230072969 + 3 ^ 40 * 3450421 * 2
def baseEnd_3450421 : Nat := 590574811122383315223103

theorem tailTrace_3450421 : CollatzResearch.WordTrace tailWord_3450421 prefixEnd_3450421 590574811122383315223103 := by
  unfold tailWord_3450421
  simp only [CollatzResearch.WordTrace]
  refine ⟨125847192632721476836535117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83898128421814317891023411 125847192632721476836535117)
  ·
    refine ⟨47192697237270553813700669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125847192632721476836535117 47192697237270553813700669)
    ·
      refine ⟨17697261463976457680137751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47192697237270553813700669 17697261463976457680137751)
      ·
        refine ⟨26545892195964686520206627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17697261463976457680137751 26545892195964686520206627)
        ·
          refine ⟨39818838293947029780309941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26545892195964686520206627 39818838293947029780309941)
          ·
            refine ⟨3733016090057534041904057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39818838293947029780309941 3733016090057534041904057)
            ·
              refine ⟨2799762067543150531428043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3733016090057534041904057 2799762067543150531428043)
              ·
                refine ⟨4199643101314725797142065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2799762067543150531428043 4199643101314725797142065)
                ·
                  refine ⟨3149732325986044347856549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4199643101314725797142065 3149732325986044347856549)
                  ·
                    refine ⟨590574811122383315223103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3149732325986044347856549 590574811122383315223103)
                    ·
                      rfl

theorem cell23_3450421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_3450421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450421 prefixEnd_3450421 := by exact prefixLift 3450421
  have htrace : WordTrace (prefixWord ++ tailWord_3450421) baseStart_3450421 baseEnd_3450421 := by
    simpa [prefixWord, tailWord_3450421, baseEnd_3450421] using wordTrace_append hprefix tailTrace_3450421
  have hstable : (prefixWord ++ tailWord_3450421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450421).length < 2 ^ (prefixWord ++ tailWord_3450421).sum := by decide
  have hdescent : baseEnd_3450421 < baseStart_3450421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450524 : List Nat := [2, 2, 3, 2, 3, 1, 2, 1, 7]
def baseStart_3450524 : Nat := 118140960795 + 3450524 * 2 ^ 59
def prefixEnd_3450524 : Nat := 4983230072969 + 3 ^ 40 * 3450524 * 2
def baseEnd_3450524 : Nat := 196864146874951449186815

theorem tailTrace_3450524 : CollatzResearch.WordTrace tailWord_3450524 prefixEnd_3450524 196864146874951449186815 := by
  unfold tailWord_3450524
  simp only [CollatzResearch.WordTrace]
  refine ⟨62925474675674162713767313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83900632900898883618356417 62925474675674162713767313)
  ·
    refine ⟨47194106006755622035325485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62925474675674162713767313 47194106006755622035325485)
    ·
      refine ⟨17697789752533358263247057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47194106006755622035325485 17697789752533358263247057)
      ·
        refine ⟨13273342314400018697435293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17697789752533358263247057 13273342314400018697435293)
        ·
          refine ⟨4977503367900007011538235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13273342314400018697435293 4977503367900007011538235)
          ·
            refine ⟨7466255051850010517307353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4977503367900007011538235 7466255051850010517307353)
            ·
              refine ⟨5599691288887507887980515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7466255051850010517307353 5599691288887507887980515)
              ·
                refine ⟨8399536933331261831970773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5599691288887507887980515 8399536933331261831970773)
                ·
                  refine ⟨196864146874951449186815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8399536933331261831970773 196864146874951449186815)
                  ·
                    rfl

theorem cell23_3450524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 7].length) (baseStart_3450524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450524 prefixEnd_3450524 := by exact prefixLift 3450524
  have htrace : WordTrace (prefixWord ++ tailWord_3450524) baseStart_3450524 baseEnd_3450524 := by
    simpa [prefixWord, tailWord_3450524, baseEnd_3450524] using wordTrace_append hprefix tailTrace_3450524
  have hstable : (prefixWord ++ tailWord_3450524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450524).length < 2 ^ (prefixWord ++ tailWord_3450524).sum := by decide
  have hdescent : baseEnd_3450524 < baseStart_3450524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450557 : List Nat := [1, 4, 1, 2, 1, 2, 1, 3, 1, 3, 4]
def baseStart_3450557 : Nat := 118140960795 + 3450557 * 2 ^ 59
def prefixEnd_3450557 : Nat := 4983230072969 + 3 ^ 40 * 3450557 * 2
def baseEnd_3450557 : Nat := 1771794266736161413568683

theorem tailTrace_3450557 : CollatzResearch.WordTrace tailWord_3450557 prefixEnd_3450557 1771794266736161413568683 := by
  unfold tailWord_3450557
  simp only [CollatzResearch.WordTrace]
  refine ⟨125852152960228772063485925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83901435306819181375657283 125852152960228772063485925)
  ·
    refine ⟨23597278680042894761903611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125852152960228772063485925 23597278680042894761903611)
    ·
      refine ⟨35395918020064342142855417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23597278680042894761903611 35395918020064342142855417)
      ·
        refine ⟨26546938515048256607141563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35395918020064342142855417 26546938515048256607141563)
        ·
          refine ⟨39820407772572384910712345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26546938515048256607141563 39820407772572384910712345)
          ·
            refine ⟨29865305829429288683034259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39820407772572384910712345 29865305829429288683034259)
            ·
              refine ⟨44797958744143933024551389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29865305829429288683034259 44797958744143933024551389)
              ·
                refine ⟨16799234529053974884206771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44797958744143933024551389 16799234529053974884206771)
                ·
                  refine ⟨25198851793580962326310157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16799234529053974884206771 25198851793580962326310157)
                  ·
                    refine ⟨9449569422592860872366309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25198851793580962326310157 9449569422592860872366309)
                    ·
                      refine ⟨1771794266736161413568683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9449569422592860872366309 1771794266736161413568683)
                      ·
                        rfl

theorem cell23_3450557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_3450557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450557 prefixEnd_3450557 := by exact prefixLift 3450557
  have htrace : WordTrace (prefixWord ++ tailWord_3450557) baseStart_3450557 baseEnd_3450557 := by
    simpa [prefixWord, tailWord_3450557, baseEnd_3450557] using wordTrace_append hprefix tailTrace_3450557
  have hstable : (prefixWord ++ tailWord_3450557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450557).length < 2 ^ (prefixWord ++ tailWord_3450557).sum := by decide
  have hdescent : baseEnd_3450557 < baseStart_3450557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450574 : List Nat := [4, 1, 1, 1, 3, 1, 3, 2, 2, 1, 4]
def baseStart_3450574 : Nat := 118140960795 + 3450574 * 2 ^ 59
def prefixEnd_3450574 : Nat := 4983230072969 + 3 ^ 40 * 3450574 * 2
def baseEnd_3450574 : Nat := 1771802995907287847056105

theorem tailTrace_3450574 : CollatzResearch.WordTrace tailWord_3450574 prefixEnd_3450574 1771802995907287847056105 := by
  unfold tailWord_3450574
  simp only [CollatzResearch.WordTrace]
  refine ⟨15731596625145897995856847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83901848667444789311236517 15731596625145897995856847)
  ·
    refine ⟨23597394937718846993785271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15731596625145897995856847 23597394937718846993785271)
    ·
      refine ⟨35396092406578270490677907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23597394937718846993785271 35396092406578270490677907)
      ·
        refine ⟨53094138609867405736016861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35396092406578270490677907 53094138609867405736016861)
        ·
          refine ⟨19910301978700277151006323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53094138609867405736016861 19910301978700277151006323)
          ·
            refine ⟨29865452968050415726509485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19910301978700277151006323 29865452968050415726509485)
            ·
              refine ⟨11199544863018905897441057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29865452968050415726509485 11199544863018905897441057)
              ·
                refine ⟨8399658647264179423080793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11199544863018905897441057 8399658647264179423080793)
                ·
                  refine ⟨6299743985448134567310595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8399658647264179423080793 6299743985448134567310595)
                  ·
                    refine ⟨9449615978172201850965893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6299743985448134567310595 9449615978172201850965893)
                    ·
                      refine ⟨1771802995907287847056105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9449615978172201850965893 1771802995907287847056105)
                      ·
                        rfl

theorem cell23_3450574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_3450574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450574 prefixEnd_3450574 := by exact prefixLift 3450574
  have htrace : WordTrace (prefixWord ++ tailWord_3450574) baseStart_3450574 baseEnd_3450574 := by
    simpa [prefixWord, tailWord_3450574, baseEnd_3450574] using wordTrace_append hprefix tailTrace_3450574
  have hstable : (prefixWord ++ tailWord_3450574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450574).length < 2 ^ (prefixWord ++ tailWord_3450574).sum := by decide
  have hdescent : baseEnd_3450574 < baseStart_3450574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450624 : List Nat := [2, 1, 1, 2, 1, 1, 2, 4, 5, 1, 3]
def baseStart_3450624 : Nat := 118140960795 + 3450624 * 2 ^ 59
def prefixEnd_3450624 : Nat := 4983230072969 + 3 ^ 40 * 3450624 * 2
def baseEnd_3450624 : Nat := 1771828669940012651430875

theorem tailTrace_3450624 : CollatzResearch.WordTrace tailWord_3450624 prefixEnd_3450624 1771828669940012651430875 := by
  unfold tailWord_3450624
  simp only [CollatzResearch.WordTrace]
  refine ⟨62927298325493021253087463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83903064433990695004116617 62927298325493021253087463)
  ·
    refine ⟨94390947488239531879631195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62927298325493021253087463 94390947488239531879631195)
    ·
      refine ⟨141586421232359297819446793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94390947488239531879631195 141586421232359297819446793)
      ·
        refine ⟨106189815924269473364585095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141586421232359297819446793 106189815924269473364585095)
        ·
          refine ⟨159284723886404210046877643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106189815924269473364585095 159284723886404210046877643)
          ·
            refine ⟨238927085829606315070316465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159284723886404210046877643 238927085829606315070316465)
            ·
              refine ⟨179195314372204736302737349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238927085829606315070316465 179195314372204736302737349)
              ·
                refine ⟨33599121444788388056763253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 179195314372204736302737349 33599121444788388056763253)
                ·
                  refine ⟨3149917635448911380321555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33599121444788388056763253 3149917635448911380321555)
                  ·
                    refine ⟨4724876453173367070482333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3149917635448911380321555 4724876453173367070482333)
                    ·
                      refine ⟨1771828669940012651430875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4724876453173367070482333 1771828669940012651430875)
                      ·
                        rfl

theorem cell23_3450624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 5, 1, 3].length) (baseStart_3450624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450624 prefixEnd_3450624 := by exact prefixLift 3450624
  have htrace : WordTrace (prefixWord ++ tailWord_3450624) baseStart_3450624 baseEnd_3450624 := by
    simpa [prefixWord, tailWord_3450624, baseEnd_3450624] using wordTrace_append hprefix tailTrace_3450624
  have hstable : (prefixWord ++ tailWord_3450624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450624).length < 2 ^ (prefixWord ++ tailWord_3450624).sum := by decide
  have hdescent : baseEnd_3450624 < baseStart_3450624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450631 : List Nat := [1, 1, 4, 4, 2, 1, 2, 2, 6]
def baseStart_3450631 : Nat := 118140960795 + 3450631 * 2 ^ 59
def prefixEnd_3450631 : Nat := 4983230072969 + 3 ^ 40 * 3450631 * 2
def baseEnd_3450631 : Nat := 196870251589399347115927

theorem tailTrace_3450631 : CollatzResearch.WordTrace tailWord_3450631 prefixEnd_3450631 196870251589399347115927 := by
  unfold tailWord_3450631
  simp only [CollatzResearch.WordTrace]
  refine ⟨125854851961960682701679747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83903234641307121801119831 125854851961960682701679747)
  ·
    refine ⟨188782277942941024052519621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125854851961960682701679747 188782277942941024052519621)
    ·
      refine ⟨35396677114301442009847429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188782277942941024052519621 35396677114301442009847429)
      ·
        refine ⟨6636876958931520376846393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35396677114301442009847429 6636876958931520376846393)
        ·
          refine ⟨4977657719198640282634795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6636876958931520376846393 4977657719198640282634795)
          ·
            refine ⟨7466486578797960423952193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4977657719198640282634795 7466486578797960423952193)
            ·
              refine ⟨5599864934098470317964145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7466486578797960423952193 5599864934098470317964145)
              ·
                refine ⟨4199898700573852738473109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5599864934098470317964145 4199898700573852738473109)
                ·
                  refine ⟨196870251589399347115927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4199898700573852738473109 196870251589399347115927)
                  ·
                    rfl

theorem cell23_3450631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 2, 6].length) (baseStart_3450631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450631 prefixEnd_3450631 := by exact prefixLift 3450631
  have htrace : WordTrace (prefixWord ++ tailWord_3450631) baseStart_3450631 baseEnd_3450631 := by
    simpa [prefixWord, tailWord_3450631, baseEnd_3450631] using wordTrace_append hprefix tailTrace_3450631
  have hstable : (prefixWord ++ tailWord_3450631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450631).length < 2 ^ (prefixWord ++ tailWord_3450631).sum := by decide
  have hdescent : baseEnd_3450631 < baseStart_3450631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450668 : List Nat := [2, 2, 1, 1, 1, 7, 1, 1, 2, 3, 2]
def baseStart_3450668 : Nat := 118140960795 + 3450668 * 2 ^ 59
def prefixEnd_3450668 : Nat := 4983230072969 + 3 ^ 40 * 3450668 * 2
def baseEnd_3450668 : Nat := 1771851263088810479280673

theorem tailTrace_3450668 : CollatzResearch.WordTrace tailWord_3450668 prefixEnd_3450668 1771851263088810479280673 := by
  unfold tailWord_3450668
  simp only [CollatzResearch.WordTrace]
  refine ⟨62928100731413319010388329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83904134308551092013851105 62928100731413319010388329)
  ·
    refine ⟨47196075548559989257791247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62928100731413319010388329 47196075548559989257791247)
    ·
      refine ⟨70794113322839983886686871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47196075548559989257791247 70794113322839983886686871)
      ·
        refine ⟨106191169984259975830030307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70794113322839983886686871 106191169984259975830030307)
        ·
          refine ⟨159286754976389963745045461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106191169984259975830030307 159286754976389963745045461)
          ·
            refine ⟨3733283319759139775274503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 159286754976389963745045461 3733283319759139775274503)
            ·
              refine ⟨5599924979638709662911755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3733283319759139775274503 5599924979638709662911755)
              ·
                refine ⟨8399887469458064494367633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5599924979638709662911755 8399887469458064494367633)
                ·
                  refine ⟨6299915602093548370775725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8399887469458064494367633 6299915602093548370775725)
                  ·
                    refine ⟨2362468350785080639040897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6299915602093548370775725 2362468350785080639040897)
                    ·
                      refine ⟨1771851263088810479280673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2362468350785080639040897 1771851263088810479280673)
                      ·
                        rfl

theorem cell23_3450668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 3, 2].length) (baseStart_3450668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450668 prefixEnd_3450668 := by exact prefixLift 3450668
  have htrace : WordTrace (prefixWord ++ tailWord_3450668) baseStart_3450668 baseEnd_3450668 := by
    simpa [prefixWord, tailWord_3450668, baseEnd_3450668] using wordTrace_append hprefix tailTrace_3450668
  have hstable : (prefixWord ++ tailWord_3450668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450668).length < 2 ^ (prefixWord ++ tailWord_3450668).sum := by decide
  have hdescent : baseEnd_3450668 < baseStart_3450668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450674 : List Nat := [3, 2, 1, 1, 3, 2, 2, 2, 1, 6]
def baseStart_3450674 : Nat := 118140960795 + 3450674 * 2 ^ 59
def prefixEnd_3450674 : Nat := 4983230072969 + 3 ^ 40 * 3450674 * 2
def baseEnd_3450674 : Nat := 590618114657579151935215

theorem tailTrace_3450674 : CollatzResearch.WordTrace tailWord_3450674 prefixEnd_3450674 590618114657579151935215 := by
  unfold tailWord_3450674
  simp only [CollatzResearch.WordTrace]
  refine ⟨31464105075201225261373769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83904280200536600696996717 31464105075201225261373769)
  ·
    refine ⟨23598078806400918946030327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31464105075201225261373769 23598078806400918946030327)
    ·
      refine ⟨35397118209601378419045491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23598078806400918946030327 35397118209601378419045491)
      ·
        refine ⟨53095677314402067628568237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35397118209601378419045491 53095677314402067628568237)
        ·
          refine ⟨19910878992900775360713089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53095677314402067628568237 19910878992900775360713089)
          ·
            refine ⟨14933159244675581520534817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19910878992900775360713089 14933159244675581520534817)
            ·
              refine ⟨11199869433506686140401113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14933159244675581520534817 11199869433506686140401113)
              ·
                refine ⟨8399902075130014605300835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11199869433506686140401113 8399902075130014605300835)
                ·
                  refine ⟨12599853112695021907951253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8399902075130014605300835 12599853112695021907951253)
                  ·
                    refine ⟨590618114657579151935215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12599853112695021907951253 590618114657579151935215)
                    ·
                      rfl

theorem cell23_3450674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 1, 6].length) (baseStart_3450674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450674 prefixEnd_3450674 := by exact prefixLift 3450674
  have htrace : WordTrace (prefixWord ++ tailWord_3450674) baseStart_3450674 baseEnd_3450674 := by
    simpa [prefixWord, tailWord_3450674, baseEnd_3450674] using wordTrace_append hprefix tailTrace_3450674
  have hstable : (prefixWord ++ tailWord_3450674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450674).length < 2 ^ (prefixWord ++ tailWord_3450674).sum := by decide
  have hdescent : baseEnd_3450674 < baseStart_3450674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450675 : List Nat := [1, 1, 1, 2, 7, 1, 2, 3, 1, 1, 3]
def baseStart_3450675 : Nat := 118140960795 + 3450675 * 2 ^ 59
def prefixEnd_3450675 : Nat := 4983230072969 + 3 ^ 40 * 3450675 * 2
def baseEnd_3450675 : Nat := 1771854857453391951893141

theorem tailTrace_3450675 : CollatzResearch.WordTrace tailWord_3450675 prefixEnd_3450675 1771854857453391951893141 := by
  unfold tailWord_3450675
  simp only [CollatzResearch.WordTrace]
  refine ⟨125856456773801278216281479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83904304515867518810854319 125856456773801278216281479)
  ·
    refine ⟨188784685160701917324422219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125856456773801278216281479 188784685160701917324422219)
    ·
      refine ⟨283177027741052875986633329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188784685160701917324422219 283177027741052875986633329)
      ·
        refine ⟨212382770805789656989974997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283177027741052875986633329 212382770805789656989974997)
        ·
          refine ⟨4977721190760695085702539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 212382770805789656989974997 4977721190760695085702539)
          ·
            refine ⟨7466581786141042628553809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4977721190760695085702539 7466581786141042628553809)
            ·
              refine ⟨5599936339605781971415357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7466581786141042628553809 5599936339605781971415357)
              ·
                refine ⟨2099976127352168239280759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5599936339605781971415357 2099976127352168239280759)
                ·
                  refine ⟨3149964191028252358921139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2099976127352168239280759 3149964191028252358921139)
                  ·
                    refine ⟨4724946286542378538381709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3149964191028252358921139 4724946286542378538381709)
                    ·
                      refine ⟨1771854857453391951893141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4724946286542378538381709 1771854857453391951893141)
                      ·
                        rfl

theorem cell23_3450675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 3, 1, 1, 3].length) (baseStart_3450675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450675 prefixEnd_3450675 := by exact prefixLift 3450675
  have htrace : WordTrace (prefixWord ++ tailWord_3450675) baseStart_3450675 baseEnd_3450675 := by
    simpa [prefixWord, tailWord_3450675, baseEnd_3450675] using wordTrace_append hprefix tailTrace_3450675
  have hstable : (prefixWord ++ tailWord_3450675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450675).length < 2 ^ (prefixWord ++ tailWord_3450675).sum := by decide
  have hdescent : baseEnd_3450675 < baseStart_3450675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450678 : List Nat := [5, 1, 2, 2, 1, 2, 1, 3, 1, 5]
def baseStart_3450678 : Nat := 118140960795 + 3450678 * 2 ^ 59
def prefixEnd_3450678 : Nat := 4983230072969 + 3 ^ 40 * 3450678 * 2
def baseEnd_3450678 : Nat := 590618799298451813385209

theorem tailTrace_3450678 : CollatzResearch.WordTrace tailWord_3450678 prefixEnd_3450678 590618799298451813385209 := by
  unfold tailWord_3450678
  simp only [CollatzResearch.WordTrace]
  refine ⟨7866035387049400608040043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83904377461860273152427125 7866035387049400608040043)
  ·
    refine ⟨11799053080574100912060065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7866035387049400608040043 11799053080574100912060065)
    ·
      refine ⟨8849289810430575684045049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11799053080574100912060065 8849289810430575684045049)
      ·
        refine ⟨6636967357822931763033787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8849289810430575684045049 6636967357822931763033787)
        ·
          refine ⟨9955451036734397644550681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6636967357822931763033787 9955451036734397644550681)
          ·
            refine ⟨7466588277550798233413011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9955451036734397644550681 7466588277550798233413011)
            ·
              refine ⟨11199882416326197350119517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7466588277550798233413011 11199882416326197350119517)
              ·
                refine ⟨4199955906122324006294819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11199882416326197350119517 4199955906122324006294819)
                ·
                  refine ⟨6299933859183486009442229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4199955906122324006294819 6299933859183486009442229)
                  ·
                    refine ⟨590618799298451813385209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6299933859183486009442229 590618799298451813385209)
                    ·
                      rfl

theorem cell23_3450678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_3450678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450678 prefixEnd_3450678 := by exact prefixLift 3450678
  have htrace : WordTrace (prefixWord ++ tailWord_3450678) baseStart_3450678 baseEnd_3450678 := by
    simpa [prefixWord, tailWord_3450678, baseEnd_3450678] using wordTrace_append hprefix tailTrace_3450678
  have hstable : (prefixWord ++ tailWord_3450678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450678).length < 2 ^ (prefixWord ++ tailWord_3450678).sum := by decide
  have hdescent : baseEnd_3450678 < baseStart_3450678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450691 : List Nat := [1, 1, 1, 3, 1, 5, 3, 2, 2, 4]
def baseStart_3450691 : Nat := 118140960795 + 3450691 * 2 ^ 59
def prefixEnd_3450691 : Nat := 4983230072969 + 3 ^ 40 * 3450691 * 2
def baseEnd_3450691 : Nat := 590621024381287963097689

theorem tailTrace_3450691 : CollatzResearch.WordTrace tailWord_3450691 prefixEnd_3450691 590621024381287963097689 := by
  unfold tailWord_3450691
  simp only [CollatzResearch.WordTrace]
  refine ⟨125857040341743312948863927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83904693561162208632575951 125857040341743312948863927)
  ·
    refine ⟨188785560512614969423295891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125857040341743312948863927 188785560512614969423295891)
    ·
      refine ⟨283178340768922454134943837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188785560512614969423295891 283178340768922454134943837)
      ·
        refine ⟨106191877788345920300603939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 283178340768922454134943837 106191877788345920300603939)
        ·
          refine ⟨159287816682518880450905909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106191877788345920300603939 159287816682518880450905909)
          ·
            refine ⟨14933232813986145042272429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 159287816682518880450905909 14933232813986145042272429)
            ·
              refine ⟨5599962305244804390852161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14933232813986145042272429 5599962305244804390852161)
              ·
                refine ⟨4199971728933603293139121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5599962305244804390852161 4199971728933603293139121)
                ·
                  refine ⟨3149978796700202469854341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4199971728933603293139121 3149978796700202469854341)
                  ·
                    refine ⟨590621024381287963097689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3149978796700202469854341 590621024381287963097689)
                    ·
                      rfl

theorem cell23_3450691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 2, 2, 4].length) (baseStart_3450691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450691 prefixEnd_3450691 := by exact prefixLift 3450691
  have htrace : WordTrace (prefixWord ++ tailWord_3450691) baseStart_3450691 baseEnd_3450691 := by
    simpa [prefixWord, tailWord_3450691, baseEnd_3450691] using wordTrace_append hprefix tailTrace_3450691
  have hstable : (prefixWord ++ tailWord_3450691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450691).length < 2 ^ (prefixWord ++ tailWord_3450691).sum := by decide
  have hdescent : baseEnd_3450691 < baseStart_3450691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450698 : List Nat := [3, 1, 2, 1, 1, 1, 6, 1, 3, 2, 2]
def baseStart_3450698 : Nat := 118140960795 + 3450698 * 2 ^ 59
def prefixEnd_3450698 : Nat := 4983230072969 + 3 ^ 40 * 3450698 * 2
def baseEnd_3450698 : Nat := 1771866667508445361905535

theorem tailTrace_3450698 : CollatzResearch.WordTrace tailWord_3450698 prefixEnd_3450698 1771866667508445361905535 := by
  unfold tailWord_3450698
  simp only [CollatzResearch.WordTrace]
  refine ⟨31464323913179488286092187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83904863768478635429579165 31464323913179488286092187)
  ·
    refine ⟨47196485869769232429138281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31464323913179488286092187 47196485869769232429138281)
    ·
      refine ⟨35397364402326924321853711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47196485869769232429138281 35397364402326924321853711)
      ·
        refine ⟨53096046603490386482780567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35397364402326924321853711 53096046603490386482780567)
        ·
          refine ⟨79644069905235579724170851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53096046603490386482780567 79644069905235579724170851)
          ·
            refine ⟨119466104857853369586256277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79644069905235579724170851 119466104857853369586256277)
            ·
              refine ⟨5599973665211876699355763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 119466104857853369586256277 5599973665211876699355763)
              ·
                refine ⟨8399960497817815049033645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5599973665211876699355763 8399960497817815049033645)
                ·
                  refine ⟨3149985186681680643387617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8399960497817815049033645 3149985186681680643387617)
                  ·
                    refine ⟨2362488890011260482540713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3149985186681680643387617 2362488890011260482540713)
                    ·
                      refine ⟨1771866667508445361905535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2362488890011260482540713 1771866667508445361905535)
                      ·
                        rfl

theorem cell23_3450698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 3, 2, 2].length) (baseStart_3450698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450698 prefixEnd_3450698 := by exact prefixLift 3450698
  have htrace : WordTrace (prefixWord ++ tailWord_3450698) baseStart_3450698 baseEnd_3450698 := by
    simpa [prefixWord, tailWord_3450698, baseEnd_3450698] using wordTrace_append hprefix tailTrace_3450698
  have hstable : (prefixWord ++ tailWord_3450698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450698).length < 2 ^ (prefixWord ++ tailWord_3450698).sum := by decide
  have hdescent : baseEnd_3450698 < baseStart_3450698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450701 : List Nat := [1, 6, 1, 2, 1, 1, 1, 1, 3, 1, 5]
def baseStart_3450701 : Nat := 118140960795 + 3450701 * 2 ^ 59
def prefixEnd_3450701 : Nat := 4983230072969 + 3 ^ 40 * 3450701 * 2
def baseEnd_3450701 : Nat := 1771868207950408850168021

theorem tailTrace_3450701 : CollatzResearch.WordTrace tailWord_3450701 prefixEnd_3450701 1771868207950408850168021 := by
  unfold tailWord_3450701
  simp only [CollatzResearch.WordTrace]
  refine ⟨125857405071707084656727957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83904936714471389771151971 125857405071707084656727957)
  ·
    refine ⟨5899565862736269593284123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 125857405071707084656727957 5899565862736269593284123)
    ·
      refine ⟨8849348794104404389926185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5899565862736269593284123 8849348794104404389926185)
      ·
        refine ⟨6637011595578303292444639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8849348794104404389926185 6637011595578303292444639)
        ·
          refine ⟨9955517393367454938666959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6637011595578303292444639 9955517393367454938666959)
          ·
            refine ⟨14933276090051182408000439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9955517393367454938666959 14933276090051182408000439)
            ·
              refine ⟨22399914135076773612000659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14933276090051182408000439 22399914135076773612000659)
              ·
                refine ⟨33599871202615160418000989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22399914135076773612000659 33599871202615160418000989)
                ·
                  refine ⟨12599951700980685156750371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33599871202615160418000989 12599951700980685156750371)
                  ·
                    refine ⟨18899927551471027735125557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12599951700980685156750371 18899927551471027735125557)
                    ·
                      refine ⟨1771868207950408850168021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18899927551471027735125557 1771868207950408850168021)
                      ·
                        rfl

theorem cell23_3450701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_3450701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450701 prefixEnd_3450701 := by exact prefixLift 3450701
  have htrace : WordTrace (prefixWord ++ tailWord_3450701) baseStart_3450701 baseEnd_3450701 := by
    simpa [prefixWord, tailWord_3450701, baseEnd_3450701] using wordTrace_append hprefix tailTrace_3450701
  have hstable : (prefixWord ++ tailWord_3450701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450701).length < 2 ^ (prefixWord ++ tailWord_3450701).sum := by decide
  have hdescent : baseEnd_3450701 < baseStart_3450701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450732 : List Nat := [2, 2, 1, 1, 4, 4, 1, 3, 1, 2, 2]
def baseStart_3450732 : Nat := 118140960795 + 3450732 * 2 ^ 59
def prefixEnd_3450732 : Nat := 4983230072969 + 3 ^ 40 * 3450732 * 2
def baseEnd_3450732 : Nat := 1771884125850698228880379

theorem tailTrace_3450732 : CollatzResearch.WordTrace tailWord_3450732 prefixEnd_3450732 1771884125850698228880379 := by
  unfold tailWord_3450732
  simp only [CollatzResearch.WordTrace]
  refine ⟨62929267867297388475553225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83905690489729851300737633 62929267867297388475553225)
  ·
    refine ⟨47196950900473041356664919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62929267867297388475553225 47196950900473041356664919)
    ·
      refine ⟨70795426350709562034997379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47196950900473041356664919 70795426350709562034997379)
      ·
        refine ⟨106193139526064343052496069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70795426350709562034997379 106193139526064343052496069)
        ·
          refine ⟨19911213661137064322343013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106193139526064343052496069 19911213661137064322343013)
          ·
            refine ⟨3733352561463199560439315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19911213661137064322343013 3733352561463199560439315)
            ·
              refine ⟨5600028842194799340658973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3733352561463199560439315 5600028842194799340658973)
              ·
                refine ⟨2100010815823049752747115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5600028842194799340658973 2100010815823049752747115)
                ·
                  refine ⟨3150016223734574629120673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2100010815823049752747115 3150016223734574629120673)
                  ·
                    refine ⟨2362512167800930971840505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3150016223734574629120673 2362512167800930971840505)
                    ·
                      refine ⟨1771884125850698228880379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2362512167800930971840505 1771884125850698228880379)
                      ·
                        rfl

theorem cell23_3450732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 3, 1, 2, 2].length) (baseStart_3450732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450732 prefixEnd_3450732 := by exact prefixLift 3450732
  have htrace : WordTrace (prefixWord ++ tailWord_3450732) baseStart_3450732 baseEnd_3450732 := by
    simpa [prefixWord, tailWord_3450732, baseEnd_3450732] using wordTrace_append hprefix tailTrace_3450732
  have hstable : (prefixWord ++ tailWord_3450732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450732).length < 2 ^ (prefixWord ++ tailWord_3450732).sum := by decide
  have hdescent : baseEnd_3450732 < baseStart_3450732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450775 : List Nat := [1, 1, 3, 3, 1, 5, 1, 2, 1, 3, 2]
def baseStart_3450775 : Nat := 118140960795 + 3450775 * 2 ^ 59
def prefixEnd_3450775 : Nat := 4983230072969 + 3 ^ 40 * 3450775 * 2
def baseEnd_3450775 : Nat := 1771906205518841560642681

theorem tailTrace_3450775 : CollatzResearch.WordTrace tailWord_3450775 prefixEnd_3450775 1771906205518841560642681 := by
  unfold tailWord_3450775
  simp only [CollatzResearch.WordTrace]
  refine ⟨125860104073438995294921779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83906736048959330196614519 125860104073438995294921779)
  ·
    refine ⟨188790156110158492942382669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125860104073438995294921779 188790156110158492942382669)
    ·
      refine ⟨70796308541309434853393501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188790156110158492942382669 70796308541309434853393501)
      ·
        refine ⟨26548615702991038070022563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70796308541309434853393501 26548615702991038070022563)
        ·
          refine ⟨39822923554486557105033845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26548615702991038070022563 39822923554486557105033845)
          ·
            refine ⟨3733399083233114728596923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39822923554486557105033845 3733399083233114728596923)
            ·
              refine ⟨5600098624849672092895385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3733399083233114728596923 5600098624849672092895385)
              ·
                refine ⟨4200073968637254069671539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5600098624849672092895385 4200073968637254069671539)
                ·
                  refine ⟨6300110952955881104507309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4200073968637254069671539 6300110952955881104507309)
                  ·
                    refine ⟨2362541607358455414190241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6300110952955881104507309 2362541607358455414190241)
                    ·
                      refine ⟨1771906205518841560642681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2362541607358455414190241 1771906205518841560642681)
                      ·
                        rfl

theorem cell23_3450775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 2, 1, 3, 2].length) (baseStart_3450775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450775 prefixEnd_3450775 := by exact prefixLift 3450775
  have htrace : WordTrace (prefixWord ++ tailWord_3450775) baseStart_3450775 baseEnd_3450775 := by
    simpa [prefixWord, tailWord_3450775, baseEnd_3450775] using wordTrace_append hprefix tailTrace_3450775
  have hstable : (prefixWord ++ tailWord_3450775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450775).length < 2 ^ (prefixWord ++ tailWord_3450775).sum := by decide
  have hdescent : baseEnd_3450775 < baseStart_3450775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450784 : List Nat := [2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 4]
def baseStart_3450784 : Nat := 118140960795 + 3450784 * 2 ^ 59
def prefixEnd_3450784 : Nat := 4983230072969 + 3 ^ 40 * 3450784 * 2
def baseEnd_3450784 : Nat := 1771910826844732025430139

theorem tailTrace_3450784 : CollatzResearch.WordTrace tailWord_3450784 prefixEnd_3450784 1771910826844732025430139 := by
  unfold tailWord_3450784
  simp only [CollatzResearch.WordTrace]
  refine ⟨62930216165203194915999703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83906954886937593221332937 62930216165203194915999703)
  ·
    refine ⟨94395324247804792373999555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62930216165203194915999703 94395324247804792373999555)
    ·
      refine ⟨141592986371707188560999333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94395324247804792373999555 141592986371707188560999333)
      ·
        refine ⟨26548684944695097855187375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141592986371707188560999333 26548684944695097855187375)
        ·
          refine ⟨39823027417042646782781063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26548684944695097855187375 39823027417042646782781063)
          ·
            refine ⟨59734541125563970174171595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39823027417042646782781063 59734541125563970174171595)
            ·
              refine ⟨89601811688345955261257393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59734541125563970174171595 89601811688345955261257393)
              ·
                refine ⟨67201358766259466445943045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89601811688345955261257393 67201358766259466445943045)
                ·
                  refine ⟨12600254768673649958614321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67201358766259466445943045 12600254768673649958614321)
                  ·
                    refine ⟨9450191076505237468960741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12600254768673649958614321 9450191076505237468960741)
                    ·
                      refine ⟨1771910826844732025430139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9450191076505237468960741 1771910826844732025430139)
                      ·
                        rfl

theorem cell23_3450784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_3450784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450784 prefixEnd_3450784 := by exact prefixLift 3450784
  have htrace : WordTrace (prefixWord ++ tailWord_3450784) baseStart_3450784 baseEnd_3450784 := by
    simpa [prefixWord, tailWord_3450784, baseEnd_3450784] using wordTrace_append hprefix tailTrace_3450784
  have hstable : (prefixWord ++ tailWord_3450784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450784).length < 2 ^ (prefixWord ++ tailWord_3450784).sum := by decide
  have hdescent : baseEnd_3450784 < baseStart_3450784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450788 : List Nat := [2, 3, 1, 2, 1, 4, 1, 2, 1, 4, 2]
def baseStart_3450788 : Nat := 118140960795 + 3450788 * 2 ^ 59
def prefixEnd_3450788 : Nat := 4983230072969 + 3 ^ 40 * 3450788 * 2
def baseEnd_3450788 : Nat := 1771912880767350009780121

theorem tailTrace_3450788 : CollatzResearch.WordTrace tailWord_3450788 prefixEnd_3450788 1771912880767350009780121 := by
  unfold tailWord_3450788
  simp only [CollatzResearch.WordTrace]
  refine ⟨62930289111195949257572509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83907052148261265676763345 62930289111195949257572509)
  ·
    refine ⟨23598858416698480971589691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62930289111195949257572509 23598858416698480971589691)
    ·
      refine ⟨35398287625047721457384537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23598858416698480971589691 35398287625047721457384537)
      ·
        refine ⟨26548715718785791093038403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35398287625047721457384537 26548715718785791093038403)
        ·
          refine ⟨39823073578178686639557605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26548715718785791093038403 39823073578178686639557605)
          ·
            refine ⟨7466826295908503744917051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39823073578178686639557605 7466826295908503744917051)
            ·
              refine ⟨11200239443862755617375577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7466826295908503744917051 11200239443862755617375577)
              ·
                refine ⟨8400179582897066713031683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11200239443862755617375577 8400179582897066713031683)
                ·
                  refine ⟨12600269374345600069547525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8400179582897066713031683 12600269374345600069547525)
                  ·
                    refine ⟨2362550507689800013040161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12600269374345600069547525 2362550507689800013040161)
                    ·
                      refine ⟨1771912880767350009780121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2362550507689800013040161 1771912880767350009780121)
                      ·
                        rfl

theorem cell23_3450788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 1, 4, 2].length) (baseStart_3450788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450788 prefixEnd_3450788 := by exact prefixLift 3450788
  have htrace : WordTrace (prefixWord ++ tailWord_3450788) baseStart_3450788 baseEnd_3450788 := by
    simpa [prefixWord, tailWord_3450788, baseEnd_3450788] using wordTrace_append hprefix tailTrace_3450788
  have hstable : (prefixWord ++ tailWord_3450788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450788).length < 2 ^ (prefixWord ++ tailWord_3450788).sum := by decide
  have hdescent : baseEnd_3450788 < baseStart_3450788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450791 : List Nat := [1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 5]
def baseStart_3450791 : Nat := 118140960795 + 3450791 * 2 ^ 59
def prefixEnd_3450791 : Nat := 4983230072969 + 3 ^ 40 * 3450791 * 2
def baseEnd_3450791 : Nat := 1771914421209313498042607

theorem tailTrace_3450791 : CollatzResearch.WordTrace tailWord_3450791 prefixEnd_3450791 1771914421209313498042607 := by
  unfold tailWord_3450791
  simp only [CollatzResearch.WordTrace]
  refine ⟨125860687641381030027504227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83907125094254020018336151 125860687641381030027504227)
  ·
    refine ⟨188791031462071545041256341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125860687641381030027504227 188791031462071545041256341)
    ·
      refine ⟨8849579599784603673808891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 188791031462071545041256341 8849579599784603673808891)
      ·
        refine ⟨13274369399676905510713337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8849579599784603673808891 13274369399676905510713337)
        ·
          refine ⟨9955777049757679133035003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13274369399676905510713337 9955777049757679133035003)
          ·
            refine ⟨14933665574636518699552505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9955777049757679133035003 14933665574636518699552505)
            ·
              refine ⟨11200249180977389024664379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14933665574636518699552505 11200249180977389024664379)
              ·
                refine ⟨16800373771466083536996569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11200249180977389024664379 16800373771466083536996569)
                ·
                  refine ⟨12600280328599562652747427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16800373771466083536996569 12600280328599562652747427)
                  ·
                    refine ⟨18900420492899343979121141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12600280328599562652747427 18900420492899343979121141)
                    ·
                      refine ⟨1771914421209313498042607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18900420492899343979121141 1771914421209313498042607)
                      ·
                        rfl

theorem cell23_3450791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_3450791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450791 prefixEnd_3450791 := by exact prefixLift 3450791
  have htrace : WordTrace (prefixWord ++ tailWord_3450791) baseStart_3450791 baseEnd_3450791 := by
    simpa [prefixWord, tailWord_3450791, baseEnd_3450791] using wordTrace_append hprefix tailTrace_3450791
  have hstable : (prefixWord ++ tailWord_3450791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450791).length < 2 ^ (prefixWord ++ tailWord_3450791).sum := by decide
  have hdescent : baseEnd_3450791 < baseStart_3450791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450805 : List Nat := [1, 3, 3, 2, 1, 2, 1, 4, 2, 2, 2]
def baseStart_3450805 : Nat := 118140960795 + 3450805 * 2 ^ 59
def prefixEnd_3450805 : Nat := 4983230072969 + 3 ^ 40 * 3450805 * 2
def baseEnd_3450805 : Nat := 1771921609938476443267543

theorem tailTrace_3450805 : CollatzResearch.WordTrace tailWord_3450805 prefixEnd_3450805 1771921609938476443267543 := by
  unfold tailWord_3450805
  simp only [CollatzResearch.WordTrace]
  refine ⟨125861198263330310418513869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83907465508886873612342579 125861198263330310418513869)
  ·
    refine ⟨47197949348748866406942701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125861198263330310418513869 47197949348748866406942701)
    ·
      refine ⟨17699231005780824902603513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47197949348748866406942701 17699231005780824902603513)
      ·
        refine ⟨13274423254335618676952635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17699231005780824902603513 13274423254335618676952635)
        ·
          refine ⟨19911634881503428015428953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13274423254335618676952635 19911634881503428015428953)
          ·
            refine ⟨14933726161127571011571715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19911634881503428015428953 14933726161127571011571715)
            ·
              refine ⟨22400589241691356517357573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14933726161127571011571715 22400589241691356517357573)
              ·
                refine ⟨4200110482817129347004545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22400589241691356517357573 4200110482817129347004545)
                ·
                  refine ⟨3150082862112847010253409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4200110482817129347004545 3150082862112847010253409)
                  ·
                    refine ⟨2362562146584635257690057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3150082862112847010253409 2362562146584635257690057)
                    ·
                      refine ⟨1771921609938476443267543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2362562146584635257690057 1771921609938476443267543)
                      ·
                        rfl

theorem cell23_3450805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_3450805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450805 prefixEnd_3450805 := by exact prefixLift 3450805
  have htrace : WordTrace (prefixWord ++ tailWord_3450805) baseStart_3450805 baseEnd_3450805 := by
    simpa [prefixWord, tailWord_3450805, baseEnd_3450805] using wordTrace_append hprefix tailTrace_3450805
  have hstable : (prefixWord ++ tailWord_3450805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450805).length < 2 ^ (prefixWord ++ tailWord_3450805).sum := by decide
  have hdescent : baseEnd_3450805 < baseStart_3450805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450831 : List Nat := [1, 1, 2, 1, 1, 5, 1, 2, 2, 5, 2]
def baseStart_3450831 : Nat := 118140960795 + 3450831 * 2 ^ 59
def prefixEnd_3450831 : Nat := 4983230072969 + 3 ^ 40 * 3450831 * 2
def baseEnd_3450831 : Nat := 1771934960435493341542423

theorem tailTrace_3450831 : CollatzResearch.WordTrace tailWord_3450831 prefixEnd_3450831 1771934960435493341542423 := by
  unfold tailWord_3450831
  simp only [CollatzResearch.WordTrace]
  refine ⟨125862146561236116858960347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83908097707490744572640231 125862146561236116858960347)
  ·
    refine ⟨188793219841854175288440521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125862146561236116858960347 188793219841854175288440521)
    ·
      refine ⟨141594914881390631466330391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188793219841854175288440521 141594914881390631466330391)
      ·
        refine ⟨212392372322085947199495587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141594914881390631466330391 212392372322085947199495587)
        ·
          refine ⟨318588558483128920799243381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212392372322085947199495587 318588558483128920799243381)
          ·
            refine ⟨29867677357793336324929067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 318588558483128920799243381 29867677357793336324929067)
            ·
              refine ⟨44801516036690004487393601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29867677357793336324929067 44801516036690004487393601)
              ·
                refine ⟨33601137027517503365545201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44801516036690004487393601 33601137027517503365545201)
                ·
                  refine ⟨25200852770638127524158901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33601137027517503365545201 25200852770638127524158901)
                  ·
                    refine ⟨2362579947247324455389897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25200852770638127524158901 2362579947247324455389897)
                    ·
                      refine ⟨1771934960435493341542423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2362579947247324455389897 1771934960435493341542423)
                      ·
                        rfl

theorem cell23_3450831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 5, 2].length) (baseStart_3450831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450831 prefixEnd_3450831 := by exact prefixLift 3450831
  have htrace : WordTrace (prefixWord ++ tailWord_3450831) baseStart_3450831 baseEnd_3450831 := by
    simpa [prefixWord, tailWord_3450831, baseEnd_3450831] using wordTrace_append hprefix tailTrace_3450831
  have hstable : (prefixWord ++ tailWord_3450831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450831).length < 2 ^ (prefixWord ++ tailWord_3450831).sum := by decide
  have hdescent : baseEnd_3450831 < baseStart_3450831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450841 : List Nat := [1, 2, 1, 2, 6, 1, 1, 1, 1, 7]
def baseStart_3450841 : Nat := 118140960795 + 3450841 * 2 ^ 59
def prefixEnd_3450841 : Nat := 4983230072969 + 3 ^ 40 * 3450841 * 2
def baseEnd_3450841 : Nat := 590646698414012767472459

theorem tailTrace_3450841 : CollatzResearch.WordTrace tailWord_3450841 prefixEnd_3450841 590646698414012767472459 := by
  unfold tailWord_3450841
  simp only [CollatzResearch.WordTrace]
  refine ⟨125862511291199888566824377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83908340860799925711216251 125862511291199888566824377)
  ·
    refine ⟨94396883468399916425118283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125862511291199888566824377 94396883468399916425118283)
    ·
      refine ⟨141595325202599874637677425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94396883468399916425118283 141595325202599874637677425)
      ·
        refine ⟨106196493901949905978258069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141595325202599874637677425 106196493901949905978258069)
        ·
          refine ⟨4977960651653901842730847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 106196493901949905978258069 4977960651653901842730847)
          ·
            refine ⟨7466940977480852764096271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4977960651653901842730847 7466940977480852764096271)
            ·
              refine ⟨11200411466221279146144407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7466940977480852764096271 11200411466221279146144407)
              ·
                refine ⟨16800617199331918719216611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11200411466221279146144407 16800617199331918719216611)
                ·
                  refine ⟨25200925798997878078824917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16800617199331918719216611 25200925798997878078824917)
                  ·
                    refine ⟨590646698414012767472459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25200925798997878078824917 590646698414012767472459)
                    ·
                      rfl

theorem cell23_3450841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 7].length) (baseStart_3450841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450841 prefixEnd_3450841 := by exact prefixLift 3450841
  have htrace : WordTrace (prefixWord ++ tailWord_3450841) baseStart_3450841 baseEnd_3450841 := by
    simpa [prefixWord, tailWord_3450841, baseEnd_3450841] using wordTrace_append hprefix tailTrace_3450841
  have hstable : (prefixWord ++ tailWord_3450841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450841).length < 2 ^ (prefixWord ++ tailWord_3450841).sum := by decide
  have hdescent : baseEnd_3450841 < baseStart_3450841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450845 : List Nat := [1, 4, 3, 1, 3, 1, 2, 3, 5]
def baseStart_3450845 : Nat := 118140960795 + 3450845 * 2 ^ 59
def prefixEnd_3450845 : Nat := 4983230072969 + 3 ^ 40 * 3450845 * 2
def baseEnd_3450845 : Nat := 196882461018295142974151

theorem tailTrace_3450845 : CollatzResearch.WordTrace tailWord_3450845 prefixEnd_3450845 196882461018295142974151 := by
  unfold tailWord_3450845
  simp only [CollatzResearch.WordTrace]
  refine ⟨125862657183185397249969989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83908438122123598166646659 125862657183185397249969989)
  ·
    refine ⟨23599248221847261984369373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125862657183185397249969989 23599248221847261984369373)
    ·
      refine ⟨8849718083192723244138515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23599248221847261984369373 8849718083192723244138515)
      ·
        refine ⟨13274577124789084866207773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8849718083192723244138515 13274577124789084866207773)
        ·
          refine ⟨4977966421795906824827915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13274577124789084866207773 4977966421795906824827915)
          ·
            refine ⟨7466949632693860237241873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4977966421795906824827915 7466949632693860237241873)
            ·
              refine ⟨5600212224520395177931405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7466949632693860237241873 5600212224520395177931405)
              ·
                refine ⟨2100079584195148191724277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5600212224520395177931405 2100079584195148191724277)
                ·
                  refine ⟨196882461018295142974151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2100079584195148191724277 196882461018295142974151)
                  ·
                    rfl

theorem cell23_3450845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 3, 5].length) (baseStart_3450845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450845 prefixEnd_3450845 := by exact prefixLift 3450845
  have htrace : WordTrace (prefixWord ++ tailWord_3450845) baseStart_3450845 baseEnd_3450845 := by
    simpa [prefixWord, tailWord_3450845, baseEnd_3450845] using wordTrace_append hprefix tailTrace_3450845
  have hstable : (prefixWord ++ tailWord_3450845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450845).length < 2 ^ (prefixWord ++ tailWord_3450845).sum := by decide
  have hdescent : baseEnd_3450845 < baseStart_3450845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450864 : List Nat := [2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 5]
def baseStart_3450864 : Nat := 118140960795 + 3450864 * 2 ^ 59
def prefixEnd_3450864 : Nat := 4983230072969 + 3 ^ 40 * 3450864 * 2
def baseEnd_3450864 : Nat := 1771951905297091712429771

theorem tailTrace_3450864 : CollatzResearch.WordTrace tailWord_3450864 prefixEnd_3450864 1771951905297091712429771 := by
  unfold tailWord_3450864
  simp only [CollatzResearch.WordTrace]
  refine ⟨62931675085058281747455823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83908900113411042329941097 62931675085058281747455823)
  ·
    refine ⟨94397512627587422621183735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62931675085058281747455823 94397512627587422621183735)
    ·
      refine ⟨141596268941381133931775603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94397512627587422621183735 141596268941381133931775603)
      ·
        refine ⟨212394403412071700897663405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141596268941381133931775603 212394403412071700897663405)
        ·
          refine ⟨79647901279526887836623777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212394403412071700897663405 79647901279526887836623777)
          ·
            refine ⟨59735925959645165877467833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79647901279526887836623777 59735925959645165877467833)
            ·
              refine ⟨44801944469733874408100875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59735925959645165877467833 44801944469733874408100875)
              ·
                refine ⟨67202916704600811612151313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44801944469733874408100875 67202916704600811612151313)
                ·
                  refine ⟨50402187528450608709113485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67202916704600811612151313 50402187528450608709113485)
                  ·
                    refine ⟨18900820323168978265917557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50402187528450608709113485 18900820323168978265917557)
                    ·
                      refine ⟨1771951905297091712429771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18900820323168978265917557 1771951905297091712429771)
                      ·
                        rfl

theorem cell23_3450864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 5].length) (baseStart_3450864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450864 prefixEnd_3450864 := by exact prefixLift 3450864
  have htrace : WordTrace (prefixWord ++ tailWord_3450864) baseStart_3450864 baseEnd_3450864 := by
    simpa [prefixWord, tailWord_3450864, baseEnd_3450864] using wordTrace_append hprefix tailTrace_3450864
  have hstable : (prefixWord ++ tailWord_3450864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450864).length < 2 ^ (prefixWord ++ tailWord_3450864).sum := by decide
  have hdescent : baseEnd_3450864 < baseStart_3450864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450878 : List Nat := [4, 2, 2, 2, 1, 1, 1, 2, 1, 3, 4]
def baseStart_3450878 : Nat := 118140960795 + 3450878 * 2 ^ 59
def prefixEnd_3450878 : Nat := 4983230072969 + 3 ^ 40 * 3450878 * 2
def baseEnd_3450878 : Nat := 1771959094026254657654707

theorem tailTrace_3450878 : CollatzResearch.WordTrace tailWord_3450878 prefixEnd_3450878 1771959094026254657654707 := by
  unfold tailWord_3450878
  simp only [CollatzResearch.WordTrace]
  refine ⟨15732982599008230485740161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83909240528043895923947525 15732982599008230485740161)
  ·
    refine ⟨11799736949256172864305121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15732982599008230485740161 11799736949256172864305121)
    ·
      refine ⟨8849802711942129648228841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11799736949256172864305121 8849802711942129648228841)
      ·
        refine ⟨6637352033956597236171631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8849802711942129648228841 6637352033956597236171631)
        ·
          refine ⟨9956028050934895854257447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6637352033956597236171631 9956028050934895854257447)
          ·
            refine ⟨14934042076402343781386171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9956028050934895854257447 14934042076402343781386171)
            ·
              refine ⟨22401063114603515672079257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14934042076402343781386171 22401063114603515672079257)
              ·
                refine ⟨16800797335952636754059443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22401063114603515672079257 16800797335952636754059443)
                ·
                  refine ⟨25201196003928955131089165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16800797335952636754059443 25201196003928955131089165)
                  ·
                    refine ⟨9450448501473358174158437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25201196003928955131089165 9450448501473358174158437)
                    ·
                      refine ⟨1771959094026254657654707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9450448501473358174158437 1771959094026254657654707)
                      ·
                        rfl

theorem cell23_3450878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_3450878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450878 prefixEnd_3450878 := by exact prefixLift 3450878
  have htrace : WordTrace (prefixWord ++ tailWord_3450878) baseStart_3450878 baseEnd_3450878 := by
    simpa [prefixWord, tailWord_3450878, baseEnd_3450878] using wordTrace_append hprefix tailTrace_3450878
  have hstable : (prefixWord ++ tailWord_3450878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450878).length < 2 ^ (prefixWord ++ tailWord_3450878).sum := by decide
  have hdescent : baseEnd_3450878 < baseStart_3450878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450881 : List Nat := [1, 2, 4, 1, 2, 1, 1, 1, 3, 4, 3]
def baseStart_3450881 : Nat := 118140960795 + 3450881 * 2 ^ 59
def prefixEnd_3450881 : Nat := 4983230072969 + 3 ^ 40 * 3450881 * 2
def baseEnd_3450881 : Nat := 1771960634468218145917193

theorem tailTrace_3450881 : CollatzResearch.WordTrace tailWord_3450881 prefixEnd_3450881 1771960634468218145917193 := by
  unfold tailWord_3450881
  simp only [CollatzResearch.WordTrace]
  refine ⟨125863970211054975398280497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83909313474036650265520331 125863970211054975398280497)
  ·
    refine ⟨94397977658291231548710373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125863970211054975398280497 94397977658291231548710373)
    ·
      refine ⟨17699620810929605915383195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94397977658291231548710373 17699620810929605915383195)
      ·
        refine ⟨26549431216394408873074793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17699620810929605915383195 26549431216394408873074793)
        ·
          refine ⟨19912073412295806654806095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26549431216394408873074793 19912073412295806654806095)
          ·
            refine ⟨29868110118443709982209143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19912073412295806654806095 29868110118443709982209143)
            ·
              refine ⟨44802165177665564973313715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29868110118443709982209143 44802165177665564973313715)
              ·
                refine ⟨67203247766498347459970573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44802165177665564973313715 67203247766498347459970573)
                ·
                  refine ⟨25201217912436880297488965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67203247766498347459970573 25201217912436880297488965)
                  ·
                    refine ⟨4725228358581915055779181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25201217912436880297488965 4725228358581915055779181)
                    ·
                      refine ⟨1771960634468218145917193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4725228358581915055779181 1771960634468218145917193)
                      ·
                        rfl

theorem cell23_3450881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_3450881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450881 prefixEnd_3450881 := by exact prefixLift 3450881
  have htrace : WordTrace (prefixWord ++ tailWord_3450881) baseStart_3450881 baseEnd_3450881 := by
    simpa [prefixWord, tailWord_3450881, baseEnd_3450881] using wordTrace_append hprefix tailTrace_3450881
  have hstable : (prefixWord ++ tailWord_3450881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450881).length < 2 ^ (prefixWord ++ tailWord_3450881).sum := by decide
  have hdescent : baseEnd_3450881 < baseStart_3450881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450938 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 6, 3, 2]
def baseStart_3450938 : Nat := 118140960795 + 3450938 * 2 ^ 59
def prefixEnd_3450938 : Nat := 4983230072969 + 3 ^ 40 * 3450938 * 2
def baseEnd_3450938 : Nat := 1771989902865524422904431

theorem tailTrace_3450938 : CollatzResearch.WordTrace tailWord_3450938 prefixEnd_3450938 1771989902865524422904431 := by
  unfold tailWord_3450938
  simp only [CollatzResearch.WordTrace]
  refine ⟨31466512292962118533276367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83910699447898982755403645 31466512292962118533276367)
  ·
    refine ⟨47199768439443177799914551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31466512292962118533276367 47199768439443177799914551)
    ·
      refine ⟨70799652659164766699871827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47199768439443177799914551 70799652659164766699871827)
      ·
        refine ⟨106199478988747150049807741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70799652659164766699871827 106199478988747150049807741)
        ·
          refine ⟨39824804620780181268677903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106199478988747150049807741 39824804620780181268677903)
          ·
            refine ⟨59737206931170271903016855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39824804620780181268677903 59737206931170271903016855)
            ·
              refine ⟨89605810396755407854525283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59737206931170271903016855 89605810396755407854525283)
              ·
                refine ⟨134408715595133111781787925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89605810396755407854525283 134408715595133111781787925)
                ·
                  refine ⟨6300408543521864614771309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 134408715595133111781787925 6300408543521864614771309)
                  ·
                    refine ⟨2362653203820699230539241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6300408543521864614771309 2362653203820699230539241)
                    ·
                      refine ⟨1771989902865524422904431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2362653203820699230539241 1771989902865524422904431)
                      ·
                        rfl

theorem cell23_3450938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 6, 3, 2].length) (baseStart_3450938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450938 prefixEnd_3450938 := by exact prefixLift 3450938
  have htrace : WordTrace (prefixWord ++ tailWord_3450938) baseStart_3450938 baseEnd_3450938 := by
    simpa [prefixWord, tailWord_3450938, baseEnd_3450938] using wordTrace_append hprefix tailTrace_3450938
  have hstable : (prefixWord ++ tailWord_3450938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450938).length < 2 ^ (prefixWord ++ tailWord_3450938).sum := by decide
  have hdescent : baseEnd_3450938 < baseStart_3450938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450965 : List Nat := [1, 3, 2, 2, 1, 4, 3, 1, 1, 5]
def baseStart_3450965 : Nat := 118140960795 + 3450965 * 2 ^ 59
def prefixEnd_3450965 : Nat := 4983230072969 + 3 ^ 40 * 3450965 * 2
def baseEnd_3450965 : Nat := 590667922281065272422269

theorem tailTrace_3450965 : CollatzResearch.WordTrace tailWord_3450965 prefixEnd_3450965 590667922281065272422269 := by
  unfold tailWord_3450965
  simp only [CollatzResearch.WordTrace]
  refine ⟨125867033942750657744338349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83911355961833771829558899 125867033942750657744338349)
  ·
    refine ⟨47200137728531496654126881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125867033942750657744338349 47200137728531496654126881)
    ·
      refine ⟨35400103296398622490595161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47200137728531496654126881 35400103296398622490595161)
      ·
        refine ⟨26550077472298966867946371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35400103296398622490595161 26550077472298966867946371)
        ·
          refine ⟨39825116208448450301919557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26550077472298966867946371 39825116208448450301919557)
          ·
            refine ⟨7467209289084084431609917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39825116208448450301919557 7467209289084084431609917)
            ·
              refine ⟨2800203483406531661853719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7467209289084084431609917 2800203483406531661853719)
              ·
                refine ⟨4200305225109797492780579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2800203483406531661853719 4200305225109797492780579)
                ·
                  refine ⟨6300457837664696239170869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4200305225109797492780579 6300457837664696239170869)
                  ·
                    refine ⟨590667922281065272422269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6300457837664696239170869 590667922281065272422269)
                    ·
                      rfl

theorem cell23_3450965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 1, 1, 5].length) (baseStart_3450965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450965 prefixEnd_3450965 := by exact prefixLift 3450965
  have htrace : WordTrace (prefixWord ++ tailWord_3450965) baseStart_3450965 baseEnd_3450965 := by
    simpa [prefixWord, tailWord_3450965, baseEnd_3450965] using wordTrace_append hprefix tailTrace_3450965
  have hstable : (prefixWord ++ tailWord_3450965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450965).length < 2 ^ (prefixWord ++ tailWord_3450965).sum := by decide
  have hdescent : baseEnd_3450965 < baseStart_3450965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450985 : List Nat := [1, 2, 1, 1, 1, 5, 2, 3, 3, 2, 2]
def baseStart_3450985 : Nat := 118140960795 + 3450985 * 2 ^ 59
def prefixEnd_3450985 : Nat := 4983230072969 + 3 ^ 40 * 3450985 * 2
def baseEnd_3450985 : Nat := 1772014036456285739016715

theorem tailTrace_3450985 : CollatzResearch.WordTrace tailWord_3450985 prefixEnd_3450985 1772014036456285739016715 := by
  unfold tailWord_3450985
  simp only [CollatzResearch.WordTrace]
  refine ⟨125867763402678201160066409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83911842268452134106710939 125867763402678201160066409)
  ·
    refine ⟨94400822552008650870049807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125867763402678201160066409 94400822552008650870049807)
    ·
      refine ⟨141601233828012976305074711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94400822552008650870049807 141601233828012976305074711)
      ·
        refine ⟨212401850742019464457612067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141601233828012976305074711 212401850742019464457612067)
        ·
          refine ⟨318602776113029196686418101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212401850742019464457612067 318602776113029196686418101)
          ·
            refine ⟨29869010260596487189351697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 318602776113029196686418101 29869010260596487189351697)
            ·
              refine ⟨22401757695447365392013773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29869010260596487189351697 22401757695447365392013773)
              ·
                refine ⟨8400659135792762022005165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22401757695447365392013773 8400659135792762022005165)
                ·
                  refine ⟨3150247175922285758251937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8400659135792762022005165 3150247175922285758251937)
                  ·
                    refine ⟨2362685381941714318688953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3150247175922285758251937 2362685381941714318688953)
                    ·
                      refine ⟨1772014036456285739016715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2362685381941714318688953 1772014036456285739016715)
                      ·
                        rfl

theorem cell23_3450985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 3, 2, 2].length) (baseStart_3450985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450985 prefixEnd_3450985 := by exact prefixLift 3450985
  have htrace : WordTrace (prefixWord ++ tailWord_3450985) baseStart_3450985 baseEnd_3450985 := by
    simpa [prefixWord, tailWord_3450985, baseEnd_3450985] using wordTrace_append hprefix tailTrace_3450985
  have hstable : (prefixWord ++ tailWord_3450985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450985).length < 2 ^ (prefixWord ++ tailWord_3450985).sum := by decide
  have hdescent : baseEnd_3450985 < baseStart_3450985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450988 : List Nat := [2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 3]
def baseStart_3450988 : Nat := 118140960795 + 3450988 * 2 ^ 59
def prefixEnd_3450988 : Nat := 4983230072969 + 3 ^ 40 * 3450988 * 2
def baseEnd_3450988 : Nat := 1772015576898249227279201

theorem tailTrace_3450988 : CollatzResearch.WordTrace tailWord_3450988 prefixEnd_3450988 1772015576898249227279201 := by
  unfold tailWord_3450988
  simp only [CollatzResearch.WordTrace]
  refine ⟨62933936410833666336212809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83911915214444888448283745 62933936410833666336212809)
  ·
    refine ⟨47200452308125249752159607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62933936410833666336212809 47200452308125249752159607)
    ·
      refine ⟨70800678462187874628239411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47200452308125249752159607 70800678462187874628239411)
      ·
        refine ⟨106201017693281811942359117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70800678462187874628239411 106201017693281811942359117)
        ·
          refine ⟨39825381634980679478384669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106201017693281811942359117 39825381634980679478384669)
          ·
            refine ⟨14934518113117754804394251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39825381634980679478384669 14934518113117754804394251)
            ·
              refine ⟨22401777169676632206591377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14934518113117754804394251 22401777169676632206591377)
              ·
                refine ⟨16801332877257474154943533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22401777169676632206591377 16801332877257474154943533)
                ·
                  refine ⟨6300499828971552808103825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16801332877257474154943533 6300499828971552808103825)
                  ·
                    refine ⟨4725374871728664606077869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6300499828971552808103825 4725374871728664606077869)
                    ·
                      refine ⟨1772015576898249227279201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4725374871728664606077869 1772015576898249227279201)
                      ·
                        rfl

theorem cell23_3450988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 3].length) (baseStart_3450988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450988 prefixEnd_3450988 := by exact prefixLift 3450988
  have htrace : WordTrace (prefixWord ++ tailWord_3450988) baseStart_3450988 baseEnd_3450988 := by
    simpa [prefixWord, tailWord_3450988, baseEnd_3450988] using wordTrace_append hprefix tailTrace_3450988
  have hstable : (prefixWord ++ tailWord_3450988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450988).length < 2 ^ (prefixWord ++ tailWord_3450988).sum := by decide
  have hdescent : baseEnd_3450988 < baseStart_3450988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3450991 : List Nat := [1, 1, 2, 1, 3, 4, 3, 8]
def baseStart_3450991 : Nat := 118140960795 + 3450991 * 2 ^ 59
def prefixEnd_3450991 : Nat := 4983230072969 + 3 ^ 40 * 3450991 * 2
def baseEnd_3450991 : Nat := 65630263605193063538581

theorem tailTrace_3450991 : CollatzResearch.WordTrace tailWord_3450991 prefixEnd_3450991 65630263605193063538581 := by
  unfold tailWord_3450991
  simp only [CollatzResearch.WordTrace]
  refine ⟨125867982240656464184784827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83911988160437642789856551 125867982240656464184784827)
  ·
    refine ⟨188801973360984696277177241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125867982240656464184784827 188801973360984696277177241)
    ·
      refine ⟨141601480020738522207882931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188801973360984696277177241 141601480020738522207882931)
      ·
        refine ⟨212402220031107783311824397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141601480020738522207882931 212402220031107783311824397)
        ·
          refine ⟨79650832511665418741934149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212402220031107783311824397 79650832511665418741934149)
          ·
            refine ⟨14934531095937266014112653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79650832511665418741934149 14934531095937266014112653)
            ·
              refine ⟨5600449160976474755292245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14934531095937266014112653 5600449160976474755292245)
              ·
                refine ⟨65630263605193063538581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5600449160976474755292245 65630263605193063538581)
                ·
                  rfl

theorem cell23_3450991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 8].length) (baseStart_3450991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3450991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3450991 prefixEnd_3450991 := by exact prefixLift 3450991
  have htrace : WordTrace (prefixWord ++ tailWord_3450991) baseStart_3450991 baseEnd_3450991 := by
    simpa [prefixWord, tailWord_3450991, baseEnd_3450991] using wordTrace_append hprefix tailTrace_3450991
  have hstable : (prefixWord ++ tailWord_3450991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3450991).length < 2 ^ (prefixWord ++ tailWord_3450991).sum := by decide
  have hdescent : baseEnd_3450991 < baseStart_3450991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3450991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451022 : List Nat := [4, 1, 1, 3, 3, 1, 1, 3, 1, 2, 3]
def baseStart_3451022 : Nat := 118140960795 + 3451022 * 2 ^ 59
def prefixEnd_3451022 : Nat := 4983230072969 + 3 ^ 40 * 3451022 * 2
def baseEnd_3451022 : Nat := 1772033035240502094254045

theorem tailTrace_3451022 : CollatzResearch.WordTrace tailWord_3451022 prefixEnd_3451022 1772033035240502094254045 := by
  unfold tailWord_3451022
  simp only [CollatzResearch.WordTrace]
  refine ⟨15733639112943019559895415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83912741935696104319442213 15733639112943019559895415)
  ·
    refine ⟨23600458669414529339843123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15733639112943019559895415 23600458669414529339843123)
    ·
      refine ⟨35400688004121794009764685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23600458669414529339843123 35400688004121794009764685)
      ·
        refine ⟨13275258001545672753661757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35400688004121794009764685 13275258001545672753661757)
        ·
          refine ⟨4978221750579627282623159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13275258001545672753661757 4978221750579627282623159)
          ·
            refine ⟨7467332625869440923934739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4978221750579627282623159 7467332625869440923934739)
            ·
              refine ⟨11200998938804161385902109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7467332625869440923934739 11200998938804161385902109)
              ·
                refine ⟨4200374602051560519713291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11200998938804161385902109 4200374602051560519713291)
                ·
                  refine ⟨6300561903077340779569937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4200374602051560519713291 6300561903077340779569937)
                  ·
                    refine ⟨4725421427308005584677453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6300561903077340779569937 4725421427308005584677453)
                    ·
                      refine ⟨1772033035240502094254045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4725421427308005584677453 1772033035240502094254045)
                      ·
                        rfl

theorem cell23_3451022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_3451022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3451022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3451022 prefixEnd_3451022 := by exact prefixLift 3451022
  have htrace : WordTrace (prefixWord ++ tailWord_3451022) baseStart_3451022 baseEnd_3451022 := by
    simpa [prefixWord, tailWord_3451022, baseEnd_3451022] using wordTrace_append hprefix tailTrace_3451022
  have hstable : (prefixWord ++ tailWord_3451022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451022).length < 2 ^ (prefixWord ++ tailWord_3451022).sum := by decide
  have hdescent : baseEnd_3451022 < baseStart_3451022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451098 : List Nat := [3, 1, 1, 2, 2, 1, 5, 1, 7]
def baseStart_3451098 : Nat := 118140960795 + 3451098 * 2 ^ 59
def prefixEnd_3451098 : Nat := 4983230072969 + 3 ^ 40 * 3451098 * 2
def baseEnd_3451098 : Nat := 196896895530027088544855

theorem tailTrace_3451098 : CollatzResearch.WordTrace tailWord_3451098 prefixEnd_3451098 196896895530027088544855 := by
  unfold tailWord_3451098
  simp only [CollatzResearch.WordTrace]
  refine ⟨31467971212817205364732487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83914589900845880972619965 31467971212817205364732487)
  ·
    refine ⟨47201956819225808047098731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31467971212817205364732487 47201956819225808047098731)
    ·
      refine ⟨70802935228838712070648097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47201956819225808047098731 70802935228838712070648097)
      ·
        refine ⟨53102201421629034052986073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70802935228838712070648097 53102201421629034052986073)
        ·
          refine ⟨39826651066221775539739555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53102201421629034052986073 39826651066221775539739555)
          ·
            refine ⟨59739976599332663309609333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39826651066221775539739555 59739976599332663309609333)
            ·
              refine ⟨5600622806187437185275875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59739976599332663309609333 5600622806187437185275875)
              ·
                refine ⟨8400934209281155777913813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5600622806187437185275875 8400934209281155777913813)
                ·
                  refine ⟨196896895530027088544855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8400934209281155777913813 196896895530027088544855)
                  ·
                    rfl

theorem cell23_3451098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 7].length) (baseStart_3451098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3451098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3451098 prefixEnd_3451098 := by exact prefixLift 3451098
  have htrace : WordTrace (prefixWord ++ tailWord_3451098) baseStart_3451098 baseEnd_3451098 := by
    simpa [prefixWord, tailWord_3451098, baseEnd_3451098] using wordTrace_append hprefix tailTrace_3451098
  have hstable : (prefixWord ++ tailWord_3451098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451098).length < 2 ^ (prefixWord ++ tailWord_3451098).sum := by decide
  have hdescent : baseEnd_3451098 < baseStart_3451098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451108 : List Nat := [2, 3, 1, 1, 1, 2, 1, 3, 1, 5, 3]
def baseStart_3451108 : Nat := 118140960795 + 3451108 * 2 ^ 59
def prefixEnd_3451108 : Nat := 4983230072969 + 3 ^ 40 * 3451108 * 2
def baseEnd_3451108 : Nat := 1772077194576788757778649

theorem tailTrace_3451108 : CollatzResearch.WordTrace tailWord_3451108 prefixEnd_3451108 1772077194576788757778649 := by
  unfold tailWord_3451108
  simp only [CollatzResearch.WordTrace]
  refine ⟨62936124790616296583396989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83914833054155062111195985 62936124790616296583396989)
  ·
    refine ⟨23601046796481111218773871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62936124790616296583396989 23601046796481111218773871)
    ·
      refine ⟨35401570194721666828160807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23601046796481111218773871 35401570194721666828160807)
      ·
        refine ⟨53102355292082500242241211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35401570194721666828160807 53102355292082500242241211)
        ·
          refine ⟨79653532938123750363361817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53102355292082500242241211 79653532938123750363361817)
          ·
            refine ⟨59740149703592812772521363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79653532938123750363361817 59740149703592812772521363)
            ·
              refine ⟨89610224555389219158782045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59740149703592812772521363 89610224555389219158782045)
              ·
                refine ⟨33603834208270957184543267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89610224555389219158782045 33603834208270957184543267)
                ·
                  refine ⟨50405751312406435776814901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33603834208270957184543267 50405751312406435776814901)
                  ·
                    refine ⟨4725539185538103354076397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50405751312406435776814901 4725539185538103354076397)
                    ·
                      refine ⟨1772077194576788757778649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4725539185538103354076397 1772077194576788757778649)
                      ·
                        rfl

theorem cell23_3451108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 1, 5, 3].length) (baseStart_3451108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3451108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3451108 prefixEnd_3451108 := by exact prefixLift 3451108
  have htrace : WordTrace (prefixWord ++ tailWord_3451108) baseStart_3451108 baseEnd_3451108 := by
    simpa [prefixWord, tailWord_3451108, baseEnd_3451108] using wordTrace_append hprefix tailTrace_3451108
  have hstable : (prefixWord ++ tailWord_3451108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451108).length < 2 ^ (prefixWord ++ tailWord_3451108).sum := by decide
  have hdescent : baseEnd_3451108 < baseStart_3451108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451109 : List Nat := [1, 3, 1, 4, 2, 2, 1, 3, 2, 2, 2]
def baseStart_3451109 : Nat := 118140960795 + 3451109 * 2 ^ 59
def prefixEnd_3451109 : Nat := 4983230072969 + 3 ^ 40 * 3451109 * 2
def baseEnd_3451109 : Nat := 1772077708057443253866145

theorem tailTrace_3451109 : CollatzResearch.WordTrace tailWord_3451109 prefixEnd_3451109 1772077708057443253866145 := by
  unfold tailWord_3451109
  simp only [CollatzResearch.WordTrace]
  refine ⟨125872286054228970337580381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83914857369485980225053587 125872286054228970337580381)
  ·
    refine ⟨47202107270335863876592643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125872286054228970337580381 47202107270335863876592643)
    ·
      refine ⟨70803160905503795814888965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47202107270335863876592643 70803160905503795814888965)
      ·
        refine ⟨13275592669781961715291681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70803160905503795814888965 13275592669781961715291681)
        ·
          refine ⟨9956694502336471286468761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13275592669781961715291681 9956694502336471286468761)
          ·
            refine ⟨7467520876752353464851571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9956694502336471286468761 7467520876752353464851571)
            ·
              refine ⟨11201281315128530197277357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7467520876752353464851571 11201281315128530197277357)
              ·
                refine ⟨4200480493173198823979009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11201281315128530197277357 4200480493173198823979009)
                ·
                  refine ⟨3150360369879899117984257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4200480493173198823979009 3150360369879899117984257)
                  ·
                    refine ⟨2362770277409924338488193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3150360369879899117984257 2362770277409924338488193)
                    ·
                      refine ⟨1772077708057443253866145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2362770277409924338488193 1772077708057443253866145)
                      ·
                        rfl

theorem cell23_3451109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_3451109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3451109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3451109 prefixEnd_3451109 := by exact prefixLift 3451109
  have htrace : WordTrace (prefixWord ++ tailWord_3451109) baseStart_3451109 baseEnd_3451109 := by
    simpa [prefixWord, tailWord_3451109, baseEnd_3451109] using wordTrace_append hprefix tailTrace_3451109
  have hstable : (prefixWord ++ tailWord_3451109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451109).length < 2 ^ (prefixWord ++ tailWord_3451109).sum := by decide
  have hdescent : baseEnd_3451109 < baseStart_3451109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451192 : List Nat := [2, 1, 2, 1, 3, 1, 3, 5, 1, 4]
def baseStart_3451192 : Nat := 118140960795 + 3451192 * 2 ^ 59
def prefixEnd_3451192 : Nat := 4983230072969 + 3 ^ 40 * 3451192 * 2
def baseEnd_3451192 : Nat := 590706775650588809709421

theorem tailTrace_3451192 : CollatzResearch.WordTrace tailWord_3451192 prefixEnd_3451192 590706775650588809709421 := by
  unfold tailWord_3451192
  simp only [CollatzResearch.WordTrace]
  refine ⟨62937656656464137756425915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83916875541952183675234553 62937656656464137756425915)
  ·
    refine ⟨94406484984696206634638873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62937656656464137756425915 94406484984696206634638873)
    ·
      refine ⟨70804863738522154975979155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94406484984696206634638873 70804863738522154975979155)
      ·
        refine ⟨106207295607783232463968733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70804863738522154975979155 106207295607783232463968733)
        ·
          refine ⟨39827735852918712173988275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106207295607783232463968733 39827735852918712173988275)
          ·
            refine ⟨59741603779378068260982413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39827735852918712173988275 59741603779378068260982413)
            ·
              refine ⟨22403101417266775597868405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59741603779378068260982413 22403101417266775597868405)
              ·
                refine ⟨2100290757868760212300163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22403101417266775597868405 2100290757868760212300163)
                ·
                  refine ⟨3150436136803140318450245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2100290757868760212300163 3150436136803140318450245)
                  ·
                    refine ⟨590706775650588809709421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3150436136803140318450245 590706775650588809709421)
                    ·
                      rfl

theorem cell23_3451192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 5, 1, 4].length) (baseStart_3451192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3451192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3451192 prefixEnd_3451192 := by exact prefixLift 3451192
  have htrace : WordTrace (prefixWord ++ tailWord_3451192) baseStart_3451192 baseEnd_3451192 := by
    simpa [prefixWord, tailWord_3451192, baseEnd_3451192] using wordTrace_append hprefix tailTrace_3451192
  have hstable : (prefixWord ++ tailWord_3451192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451192).length < 2 ^ (prefixWord ++ tailWord_3451192).sum := by decide
  have hdescent : baseEnd_3451192 < baseStart_3451192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451208 : List Nat := [2, 1, 3, 1, 1, 2, 3, 1, 1, 2, 6]
def baseStart_3451208 : Nat := 118140960795 + 3451208 * 2 ^ 59
def prefixEnd_3451208 : Nat := 4983230072969 + 3 ^ 40 * 3451208 * 2
def baseEnd_3451208 : Nat := 1772128542642238366528189

theorem tailTrace_3451208 : CollatzResearch.WordTrace tailWord_3451208 prefixEnd_3451208 1772128542642238366528189 := by
  unfold tailWord_3451208
  simp only [CollatzResearch.WordTrace]
  refine ⟨62937948440435155122717139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83917264587246873496956185 62937948440435155122717139)
  ·
    refine ⟨94406922660652732684075709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62937948440435155122717139 94406922660652732684075709)
    ·
      refine ⟨35402595997744774756528391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94406922660652732684075709 35402595997744774756528391)
      ·
        refine ⟨53103893996617162134792587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35402595997744774756528391 53103893996617162134792587)
        ·
          refine ⟨79655840994925743202188881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53103893996617162134792587 79655840994925743202188881)
          ·
            refine ⟨59741880746194307401641661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79655840994925743202188881 59741880746194307401641661)
            ·
              refine ⟨22403205279822865275615623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59741880746194307401641661 22403205279822865275615623)
              ·
                refine ⟨33604807919734297913423435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22403205279822865275615623 33604807919734297913423435)
                ·
                  refine ⟨50407211879601446870135153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33604807919734297913423435 50407211879601446870135153)
                  ·
                    refine ⟨37805408909701085152601365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50407211879601446870135153 37805408909701085152601365)
                    ·
                      refine ⟨1772128542642238366528189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37805408909701085152601365 1772128542642238366528189)
                      ·
                        rfl

theorem cell23_3451208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_3451208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3451208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3451208 prefixEnd_3451208 := by exact prefixLift 3451208
  have htrace : WordTrace (prefixWord ++ tailWord_3451208) baseStart_3451208 baseEnd_3451208 := by
    simpa [prefixWord, tailWord_3451208, baseEnd_3451208] using wordTrace_append hprefix tailTrace_3451208
  have hstable : (prefixWord ++ tailWord_3451208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451208).length < 2 ^ (prefixWord ++ tailWord_3451208).sum := by decide
  have hdescent : baseEnd_3451208 < baseStart_3451208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451275 : List Nat := [1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 5]
def baseStart_3451275 : Nat := 118140960795 + 3451275 * 2 ^ 59
def prefixEnd_3451275 : Nat := 4983230072969 + 3 ^ 40 * 3451275 * 2
def baseEnd_3451275 : Nat := 1772162945846089604390381

theorem tailTrace_3451275 : CollatzResearch.WordTrace tailWord_3451275 prefixEnd_3451275 1772162945846089604390381 := by
  unfold tailWord_3451275
  simp only [CollatzResearch.WordTrace]
  refine ⟨125878340571627580688123279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83918893714418387125415519 125878340571627580688123279)
  ·
    refine ⟨188817510857441371032184919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125878340571627580688123279 188817510857441371032184919)
    ·
      refine ⟨283226266286162056548277379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188817510857441371032184919 283226266286162056548277379)
      ·
        refine ⟨424839399429243084822416069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283226266286162056548277379 424839399429243084822416069)
        ·
          refine ⟨79657387392983078404203013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 424839399429243084822416069 79657387392983078404203013)
          ·
            refine ⟨14935760136184327200788065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79657387392983078404203013 14935760136184327200788065)
            ·
              refine ⟨11201820102138245400591049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14935760136184327200788065 11201820102138245400591049)
              ·
                refine ⟨8401365076603684050443287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11201820102138245400591049 8401365076603684050443287)
                ·
                  refine ⟨12602047614905526075664931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8401365076603684050443287 12602047614905526075664931)
                  ·
                    refine ⟨18903071422358289113497397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12602047614905526075664931 18903071422358289113497397)
                    ·
                      refine ⟨1772162945846089604390381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18903071422358289113497397 1772162945846089604390381)
                      ·
                        rfl

theorem cell23_3451275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 5].length) (baseStart_3451275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3451275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3451275 prefixEnd_3451275 := by exact prefixLift 3451275
  have htrace : WordTrace (prefixWord ++ tailWord_3451275) baseStart_3451275 baseEnd_3451275 := by
    simpa [prefixWord, tailWord_3451275, baseEnd_3451275] using wordTrace_append hprefix tailTrace_3451275
  have hstable : (prefixWord ++ tailWord_3451275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451275).length < 2 ^ (prefixWord ++ tailWord_3451275).sum := by decide
  have hdescent : baseEnd_3451275 < baseStart_3451275 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451285 : List Nat := [1, 3, 2, 1, 1, 2, 1, 5, 1, 2, 4]
def baseStart_3451285 : Nat := 118140960795 + 3451285 * 2 ^ 59
def prefixEnd_3451285 : Nat := 4983230072969 + 3 ^ 40 * 3451285 * 2
def baseEnd_3451285 : Nat := 1772168080652634565265335

theorem tailTrace_3451285 : CollatzResearch.WordTrace tailWord_3451285 prefixEnd_3451285 1772168080652634565265335 := by
  unfold tailWord_3451285
  simp only [CollatzResearch.WordTrace]
  refine ⟨125878705301591352395987309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83919136867727568263991539 125878705301591352395987309)
  ·
    refine ⟨47204514488096757148495241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125878705301591352395987309 47204514488096757148495241)
    ·
      refine ⟨35403385866072567861371431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47204514488096757148495241 35403385866072567861371431)
      ·
        refine ⟨53105078799108851792057147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35403385866072567861371431 53105078799108851792057147)
        ·
          refine ⟨79657618198663277688085721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53105078799108851792057147 79657618198663277688085721)
          ·
            refine ⟨59743213648997458266064291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79657618198663277688085721 59743213648997458266064291)
            ·
              refine ⟨89614820473496187399096437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59743213648997458266064291 89614820473496187399096437)
              ·
                refine ⟨8401389419390267568665291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89614820473496187399096437 8401389419390267568665291)
                ·
                  refine ⟨12602084129085401352997937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8401389419390267568665291 12602084129085401352997937)
                  ·
                    refine ⟨9451563096814051014748453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12602084129085401352997937 9451563096814051014748453)
                    ·
                      refine ⟨1772168080652634565265335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9451563096814051014748453 1772168080652634565265335)
                      ·
                        rfl

theorem cell23_3451285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_3451285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3451285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3451285 prefixEnd_3451285 := by exact prefixLift 3451285
  have htrace : WordTrace (prefixWord ++ tailWord_3451285) baseStart_3451285 baseEnd_3451285 := by
    simpa [prefixWord, tailWord_3451285, baseEnd_3451285] using wordTrace_append hprefix tailTrace_3451285
  have hstable : (prefixWord ++ tailWord_3451285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451285).length < 2 ^ (prefixWord ++ tailWord_3451285).sum := by decide
  have hdescent : baseEnd_3451285 < baseStart_3451285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451322 : List Nat := [3, 1, 1, 1, 2, 1, 1, 5, 4, 1, 3]
def baseStart_3451322 : Nat := 118140960795 + 3451322 * 2 ^ 59
def prefixEnd_3451322 : Nat := 4983230072969 + 3 ^ 40 * 3451322 * 2
def baseEnd_3451322 : Nat := 1772187079436850920502665

theorem tailTrace_3451322 : CollatzResearch.WordTrace tailWord_3451322 prefixEnd_3451322 1772187079436850920502665 := by
  unfold tailWord_3451322
  simp only [CollatzResearch.WordTrace]
  refine ⟨31470013700614326928771055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83920036534971538476722813 31470013700614326928771055)
  ·
    refine ⟨47205020550921490393156583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31470013700614326928771055 47205020550921490393156583)
    ·
      refine ⟨70807530826382235589734875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47205020550921490393156583 70807530826382235589734875)
      ·
        refine ⟨106211296239573353384602313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70807530826382235589734875 106211296239573353384602313)
        ·
          refine ⟨79658472179680015038451735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106211296239573353384602313 79658472179680015038451735)
          ·
            refine ⟨119487708269520022557677603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79658472179680015038451735 119487708269520022557677603)
            ·
              refine ⟨179231562404280033836516405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119487708269520022557677603 179231562404280033836516405)
              ·
                refine ⟨16802958975401253172173413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 179231562404280033836516405 16802958975401253172173413)
                ·
                  refine ⟨3150554807887734969782515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16802958975401253172173413 3150554807887734969782515)
                  ·
                    refine ⟨4725832211831602454673773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3150554807887734969782515 4725832211831602454673773)
                    ·
                      refine ⟨1772187079436850920502665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4725832211831602454673773 1772187079436850920502665)
                      ·
                        rfl

theorem cell23_3451322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 4, 1, 3].length) (baseStart_3451322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3451322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3451322 prefixEnd_3451322 := by exact prefixLift 3451322
  have htrace : WordTrace (prefixWord ++ tailWord_3451322) baseStart_3451322 baseEnd_3451322 := by
    simpa [prefixWord, tailWord_3451322, baseEnd_3451322] using wordTrace_append hprefix tailTrace_3451322
  have hstable : (prefixWord ++ tailWord_3451322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451322).length < 2 ^ (prefixWord ++ tailWord_3451322).sum := by decide
  have hdescent : baseEnd_3451322 < baseStart_3451322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451325 : List Nat := [1, 4, 1, 2, 2, 2, 1, 1, 2, 7]
def baseStart_3451325 : Nat := 118140960795 + 3451325 * 2 ^ 59
def prefixEnd_3451325 : Nat := 4983230072969 + 3 ^ 40 * 3451325 * 2
def baseEnd_3451325 : Nat := 590729539959604802921717

theorem tailTrace_3451325 : CollatzResearch.WordTrace tailWord_3451325 prefixEnd_3451325 590729539959604802921717 := by
  unfold tailWord_3451325
  simp only [CollatzResearch.WordTrace]
  refine ⟨125880164221446439227443429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83920109480964292818295619 125880164221446439227443429)
  ·
    refine ⟨23602530791521207355145643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125880164221446439227443429 23602530791521207355145643)
    ·
      refine ⟨35403796187281811032718465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23602530791521207355145643 35403796187281811032718465)
      ·
        refine ⟨26552847140461358274538849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35403796187281811032718465 26552847140461358274538849)
        ·
          refine ⟨19914635355346018705904137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26552847140461358274538849 19914635355346018705904137)
          ·
            refine ⟨14935976516509514029428103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19914635355346018705904137 14935976516509514029428103)
            ·
              refine ⟨22403964774764271044142155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14935976516509514029428103 22403964774764271044142155)
              ·
                refine ⟨33605947162146406566213233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22403964774764271044142155 33605947162146406566213233)
                ·
                  refine ⟨25204460371609804924659925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33605947162146406566213233 25204460371609804924659925)
                  ·
                    refine ⟨590729539959604802921717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25204460371609804924659925 590729539959604802921717)
                    ·
                      rfl

theorem cell23_3451325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 7].length) (baseStart_3451325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3451325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3451325 prefixEnd_3451325 := by exact prefixLift 3451325
  have htrace : WordTrace (prefixWord ++ tailWord_3451325) baseStart_3451325 baseEnd_3451325 := by
    simpa [prefixWord, tailWord_3451325, baseEnd_3451325] using wordTrace_append hprefix tailTrace_3451325
  have hstable : (prefixWord ++ tailWord_3451325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451325).length < 2 ^ (prefixWord ++ tailWord_3451325).sum := by decide
  have hdescent : baseEnd_3451325 < baseStart_3451325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451349 : List Nat := [1, 3, 2, 3, 1, 2, 2, 1, 3, 3, 2]
def baseStart_3451349 : Nat := 118140960795 + 3451349 * 2 ^ 59
def prefixEnd_3451349 : Nat := 4983230072969 + 3 ^ 40 * 3451349 * 2
def baseEnd_3451349 : Nat := 1772200943414522314865041

theorem tailTrace_3451349 : CollatzResearch.WordTrace tailWord_3451349 prefixEnd_3451349 1772200943414522314865041 := by
  unfold tailWord_3451349
  simp only [CollatzResearch.WordTrace]
  refine ⟨125881039573359491326317101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83920693048906327550878067 125881039573359491326317101)
  ·
    refine ⟨47205389840009809247368913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125881039573359491326317101 47205389840009809247368913)
    ·
      refine ⟨35404042380007356935526685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47205389840009809247368913 35404042380007356935526685)
      ·
        refine ⟨13276515892502758850822507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35404042380007356935526685 13276515892502758850822507)
        ·
          refine ⟨19914773838754138276233761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13276515892502758850822507 19914773838754138276233761)
          ·
            refine ⟨14936080379065603707175321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19914773838754138276233761 14936080379065603707175321)
            ·
              refine ⟨11202060284299202780381491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14936080379065603707175321 11202060284299202780381491)
              ·
                refine ⟨16803090426448804170572237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11202060284299202780381491 16803090426448804170572237)
                ·
                  refine ⟨6301158909918301563964589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16803090426448804170572237 6301158909918301563964589)
                  ·
                    refine ⟨2362934591219363086486721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6301158909918301563964589 2362934591219363086486721)
                    ·
                      refine ⟨1772200943414522314865041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2362934591219363086486721 1772200943414522314865041)
                      ·
                        rfl

theorem cell23_3451349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_3451349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3451349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3451349 prefixEnd_3451349 := by exact prefixLift 3451349
  have htrace : WordTrace (prefixWord ++ tailWord_3451349) baseStart_3451349 baseEnd_3451349 := by
    simpa [prefixWord, tailWord_3451349, baseEnd_3451349] using wordTrace_append hprefix tailTrace_3451349
  have hstable : (prefixWord ++ tailWord_3451349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451349).length < 2 ^ (prefixWord ++ tailWord_3451349).sum := by decide
  have hdescent : baseEnd_3451349 < baseStart_3451349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451373 : List Nat := [1, 5, 1, 3, 1, 3, 1, 2, 2, 1, 3]
def baseStart_3451373 : Nat := 118140960795 + 3451373 * 2 ^ 59
def prefixEnd_3451373 : Nat := 4983230072969 + 3 ^ 40 * 3451373 * 2
def baseEnd_3451373 : Nat := 1772213266950230220964931

theorem tailTrace_3451373 : CollatzResearch.WordTrace tailWord_3451373 prefixEnd_3451373 1772213266950230220964931 := by
  unfold tailWord_3451373
  simp only [CollatzResearch.WordTrace]
  refine ⟨125881914925272543425190773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83921276616848362283460515 125881914925272543425190773)
  ·
    refine ⟨11801429524244300946111635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125881914925272543425190773 11801429524244300946111635)
    ·
      refine ⟨17702144286366451419167453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11801429524244300946111635 17702144286366451419167453)
      ·
        refine ⟨6638304107387419282187795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17702144286366451419167453 6638304107387419282187795)
        ·
          refine ⟨9957456161081128923281693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6638304107387419282187795 9957456161081128923281693)
          ·
            refine ⟨3734046060405423346230635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9957456161081128923281693 3734046060405423346230635)
            ·
              refine ⟨5601069090608135019345953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3734046060405423346230635 5601069090608135019345953)
              ·
                refine ⟨4200801817956101264509465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5601069090608135019345953 4200801817956101264509465)
                ·
                  refine ⟨3150601363467075948382099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4200801817956101264509465 3150601363467075948382099)
                  ·
                    refine ⟨4725902045200613922573149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3150601363467075948382099 4725902045200613922573149)
                    ·
                      refine ⟨1772213266950230220964931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4725902045200613922573149 1772213266950230220964931)
                      ·
                        rfl

theorem cell23_3451373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_3451373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3451373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3451373 prefixEnd_3451373 := by exact prefixLift 3451373
  have htrace : WordTrace (prefixWord ++ tailWord_3451373) baseStart_3451373 baseEnd_3451373 := by
    simpa [prefixWord, tailWord_3451373, baseEnd_3451373] using wordTrace_append hprefix tailTrace_3451373
  have hstable : (prefixWord ++ tailWord_3451373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451373).length < 2 ^ (prefixWord ++ tailWord_3451373).sum := by decide
  have hdescent : baseEnd_3451373 < baseStart_3451373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451379 : List Nat := [1, 1, 1, 2, 2, 2, 5, 1, 4, 2, 2]
def baseStart_3451379 : Nat := 118140960795 + 3451379 * 2 ^ 59
def prefixEnd_3451379 : Nat := 4983230072969 + 3 ^ 40 * 3451379 * 2
def baseEnd_3451379 : Nat := 1772216347834157197489903

theorem tailTrace_3451379 : CollatzResearch.WordTrace tailWord_3451379 prefixEnd_3451379 1772216347834157197489903 := by
  unfold tailWord_3451379
  simp only [CollatzResearch.WordTrace]
  refine ⟨125882133763250806449909191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83921422508833870966606127 125882133763250806449909191)
  ·
    refine ⟨188823200644876209674863787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125882133763250806449909191 188823200644876209674863787)
    ·
      refine ⟨283234800967314314512295681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188823200644876209674863787 283234800967314314512295681)
      ·
        refine ⟨212426100725485735884221761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283234800967314314512295681 212426100725485735884221761)
        ·
          refine ⟨159319575544114301913166321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212426100725485735884221761 159319575544114301913166321)
          ·
            refine ⟨119489681658085726434874741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159319575544114301913166321 119489681658085726434874741)
            ·
              refine ⟨11202157655445536853269507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 119489681658085726434874741 11202157655445536853269507)
              ·
                refine ⟨16803236483168305279904261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11202157655445536853269507 16803236483168305279904261)
                ·
                  refine ⟨3150606840594057239982049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16803236483168305279904261 3150606840594057239982049)
                  ·
                    refine ⟨2362955130445542929986537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3150606840594057239982049 2362955130445542929986537)
                    ·
                      refine ⟨1772216347834157197489903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2362955130445542929986537 1772216347834157197489903)
                      ·
                        rfl

theorem cell23_3451379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 4, 2, 2].length) (baseStart_3451379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3451379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3451379 prefixEnd_3451379 := by exact prefixLift 3451379
  have htrace : WordTrace (prefixWord ++ tailWord_3451379) baseStart_3451379 baseEnd_3451379 := by
    simpa [prefixWord, tailWord_3451379, baseEnd_3451379] using wordTrace_append hprefix tailTrace_3451379
  have hstable : (prefixWord ++ tailWord_3451379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451379).length < 2 ^ (prefixWord ++ tailWord_3451379).sum := by decide
  have hdescent : baseEnd_3451379 < baseStart_3451379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451385 : List Nat := [1, 2, 1, 3, 1, 2, 3, 3, 7]
def baseStart_3451385 : Nat := 118140960795 + 3451385 * 2 ^ 59
def prefixEnd_3451385 : Nat := 4983230072969 + 3 ^ 40 * 3451385 * 2
def baseEnd_3451385 : Nat := 196913269857564908223875

theorem tailTrace_3451385 : CollatzResearch.WordTrace tailWord_3451385 prefixEnd_3451385 196913269857564908223875 := by
  unfold tailWord_3451385
  simp only [CollatzResearch.WordTrace]
  refine ⟨125882352601229069474627609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83921568400819379649751739 125882352601229069474627609)
  ·
    refine ⟨94411764450921802105970707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125882352601229069474627609 94411764450921802105970707)
    ·
      refine ⟨141617646676382703158956061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94411764450921802105970707 141617646676382703158956061)
      ·
        refine ⟨53106617503643513684608523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141617646676382703158956061 53106617503643513684608523)
        ·
          refine ⟨79659926255465270526912785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53106617503643513684608523 79659926255465270526912785)
          ·
            refine ⟨59744944691598952895184589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79659926255465270526912785 59744944691598952895184589)
            ·
              refine ⟨22404354259349607335694221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59744944691598952895184589 22404354259349607335694221)
              ·
                refine ⟨8401632847256102750885333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22404354259349607335694221 8401632847256102750885333)
                ·
                  refine ⟨196913269857564908223875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8401632847256102750885333 196913269857564908223875)
                  ·
                    rfl

theorem cell23_3451385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 7].length) (baseStart_3451385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3451385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3451385 prefixEnd_3451385 := by exact prefixLift 3451385
  have htrace : WordTrace (prefixWord ++ tailWord_3451385) baseStart_3451385 baseEnd_3451385 := by
    simpa [prefixWord, tailWord_3451385, baseEnd_3451385] using wordTrace_append hprefix tailTrace_3451385
  have hstable : (prefixWord ++ tailWord_3451385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451385).length < 2 ^ (prefixWord ++ tailWord_3451385).sum := by decide
  have hdescent : baseEnd_3451385 < baseStart_3451385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451396 : List Nat := [2, 3, 2, 3, 1, 1, 3, 1, 1, 4, 2]
def baseStart_3451396 : Nat := 118140960795 + 3451396 * 2 ^ 59
def prefixEnd_3451396 : Nat := 4983230072969 + 3 ^ 40 * 3451396 * 2
def baseEnd_3451396 : Nat := 1772225077005283630977325

theorem tailTrace_3451396 : CollatzResearch.WordTrace tailWord_3451396 prefixEnd_3451396 1772225077005283630977325 := by
  unfold tailWord_3451396
  simp only [CollatzResearch.WordTrace]
  refine ⟨62941376902094609176639021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83921835869459478902185361 62941376902094609176639021)
  ·
    refine ⟨23603016338285478441239633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62941376902094609176639021 23603016338285478441239633)
    ·
      refine ⟨17702262253714108830929725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23603016338285478441239633 17702262253714108830929725)
      ·
        refine ⟨6638348345142790811598647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17702262253714108830929725 6638348345142790811598647)
        ·
          refine ⟨9957522517714186217397971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6638348345142790811598647 9957522517714186217397971)
          ·
            refine ⟨14936283776571279326096957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9957522517714186217397971 14936283776571279326096957)
            ·
              refine ⟨5601106416214229747286359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14936283776571279326096957 5601106416214229747286359)
              ·
                refine ⟨8401659624321344620929539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5601106416214229747286359 8401659624321344620929539)
                ·
                  refine ⟨12602489436482016931394309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8401659624321344620929539 12602489436482016931394309)
                  ·
                    refine ⟨2362966769340378174636433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12602489436482016931394309 2362966769340378174636433)
                    ·
                      refine ⟨1772225077005283630977325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2362966769340378174636433 1772225077005283630977325)
                      ·
                        rfl

theorem cell23_3451396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_3451396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3451396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3451396 prefixEnd_3451396 := by exact prefixLift 3451396
  have htrace : WordTrace (prefixWord ++ tailWord_3451396) baseStart_3451396 baseEnd_3451396 := by
    simpa [prefixWord, tailWord_3451396, baseEnd_3451396] using wordTrace_append hprefix tailTrace_3451396
  have hstable : (prefixWord ++ tailWord_3451396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451396).length < 2 ^ (prefixWord ++ tailWord_3451396).sum := by decide
  have hdescent : baseEnd_3451396 < baseStart_3451396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451465 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 3, 3, 6]
def baseStart_3451465 : Nat := 118140960795 + 3451465 * 2 ^ 59
def prefixEnd_3451465 : Nat := 4983230072969 + 3 ^ 40 * 3451465 * 2
def baseEnd_3451465 : Nat := 1772260507170443861014507

theorem tailTrace_3451465 : CollatzResearch.WordTrace tailWord_3451465 prefixEnd_3451465 1772260507170443861014507 := by
  unfold tailWord_3451465
  simp only [CollatzResearch.WordTrace]
  refine ⟨125885270440939243137539849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83923513627292828758359899 125885270440939243137539849)
  ·
    refine ⟨94413952830704432353154887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125885270440939243137539849 94413952830704432353154887)
    ·
      refine ⟨141620929246056648529732331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94413952830704432353154887 141620929246056648529732331)
      ·
        refine ⟨212431393869084972794598497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141620929246056648529732331 212431393869084972794598497)
        ·
          refine ⟨159323545401813729595948873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212431393869084972794598497 159323545401813729595948873)
          ·
            refine ⟨119492659051360297196961655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159323545401813729595948873 119492659051360297196961655)
            ·
              refine ⟨179238988577040445795442483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119492659051360297196961655 179238988577040445795442483)
              ·
                refine ⟨268858482865560668693163725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179238988577040445795442483 268858482865560668693163725)
                ·
                  refine ⟨100821931074585250759936397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 268858482865560668693163725 100821931074585250759936397)
                  ·
                    refine ⟨37808224152969469034976149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 100821931074585250759936397 37808224152969469034976149)
                    ·
                      refine ⟨1772260507170443861014507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37808224152969469034976149 1772260507170443861014507)
                      ·
                        rfl

theorem cell23_3451465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 3, 6].length) (baseStart_3451465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3451465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3451465 prefixEnd_3451465 := by exact prefixLift 3451465
  have htrace : WordTrace (prefixWord ++ tailWord_3451465) baseStart_3451465 baseEnd_3451465 := by
    simpa [prefixWord, tailWord_3451465, baseEnd_3451465] using wordTrace_append hprefix tailTrace_3451465
  have hstable : (prefixWord ++ tailWord_3451465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451465).length < 2 ^ (prefixWord ++ tailWord_3451465).sum := by decide
  have hdescent : baseEnd_3451465 < baseStart_3451465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451489 : List Nat := [1, 2, 3, 1, 1, 4, 2, 2, 2, 2, 3]
def baseStart_3451489 : Nat := 118140960795 + 3451489 * 2 ^ 59
def prefixEnd_3451489 : Nat := 4983230072969 + 3 ^ 40 * 3451489 * 2
def baseEnd_3451489 : Nat := 1772272830706151767114397

theorem tailTrace_3451489 : CollatzResearch.WordTrace tailWord_3451489 prefixEnd_3451489 1772272830706151767114397 := by
  unfold tailWord_3451489
  simp only [CollatzResearch.WordTrace]
  refine ⟨125886145792852295236413521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83924097195234863490942347 125886145792852295236413521)
  ·
    refine ⟨94414609344639221427310141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125886145792852295236413521 94414609344639221427310141)
    ·
      refine ⟨35405478504239708035241303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94414609344639221427310141 35405478504239708035241303)
      ·
        refine ⟨53108217756359562052861955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35405478504239708035241303 53108217756359562052861955)
        ·
          refine ⟨79662326634539343079292933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53108217756359562052861955 79662326634539343079292933)
          ·
            refine ⟨14936686243976126827367425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79662326634539343079292933 14936686243976126827367425)
            ·
              refine ⟨11202514682982095120525569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14936686243976126827367425 11202514682982095120525569)
              ·
                refine ⟨8401886012236571340394177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11202514682982095120525569 8401886012236571340394177)
                ·
                  refine ⟨6301414509177428505295633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8401886012236571340394177 6301414509177428505295633)
                  ·
                    refine ⟨4726060881883071378971725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6301414509177428505295633 4726060881883071378971725)
                    ·
                      refine ⟨1772272830706151767114397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4726060881883071378971725 1772272830706151767114397)
                      ·
                        rfl

theorem cell23_3451489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 2, 2, 3].length) (baseStart_3451489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3451489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3451489 prefixEnd_3451489 := by exact prefixLift 3451489
  have htrace : WordTrace (prefixWord ++ tailWord_3451489) baseStart_3451489 baseEnd_3451489 := by
    simpa [prefixWord, tailWord_3451489, baseEnd_3451489] using wordTrace_append hprefix tailTrace_3451489
  have hstable : (prefixWord ++ tailWord_3451489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451489).length < 2 ^ (prefixWord ++ tailWord_3451489).sum := by decide
  have hdescent : baseEnd_3451489 < baseStart_3451489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451553 : List Nat := [1, 2, 3, 3, 3, 1, 2, 1, 3, 1, 3]
def baseStart_3451553 : Nat := 118140960795 + 3451553 * 2 ^ 59
def prefixEnd_3451553 : Nat := 4983230072969 + 3 ^ 40 * 3451553 * 2
def baseEnd_3451553 : Nat := 1772305693468039516714103

theorem tailTrace_3451553 : CollatzResearch.WordTrace tailWord_3451553 prefixEnd_3451553 1772305693468039516714103 := by
  unfold tailWord_3451553
  simp only [CollatzResearch.WordTrace]
  refine ⟨125888480064620434166743313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83925653376413622777828875 125888480064620434166743313)
  ·
    refine ⟨94416360048465325625057485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125888480064620434166743313 94416360048465325625057485)
    ·
      refine ⟨35406135018174497109396557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94416360048465325625057485 35406135018174497109396557)
      ·
        refine ⟨13277300631815436416023709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35406135018174497109396557 13277300631815436416023709)
        ·
          refine ⟨4978987736930788656008891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13277300631815436416023709 4978987736930788656008891)
          ·
            refine ⟨7468481605396182984013337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4978987736930788656008891 7468481605396182984013337)
            ·
              refine ⟨5601361204047137238010003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7468481605396182984013337 5601361204047137238010003)
              ·
                refine ⟨8402041806070705857015005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5601361204047137238010003 8402041806070705857015005)
                ·
                  refine ⟨3150765677276514696380627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8402041806070705857015005 3150765677276514696380627)
                  ·
                    refine ⟨4726148515914772044570941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3150765677276514696380627 4726148515914772044570941)
                    ·
                      refine ⟨1772305693468039516714103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4726148515914772044570941 1772305693468039516714103)
                      ·
                        rfl

theorem cell23_3451553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_3451553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3451553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3451553 prefixEnd_3451553 := by exact prefixLift 3451553
  have htrace : WordTrace (prefixWord ++ tailWord_3451553) baseStart_3451553 baseEnd_3451553 := by
    simpa [prefixWord, tailWord_3451553, baseEnd_3451553] using wordTrace_append hprefix tailTrace_3451553
  have hstable : (prefixWord ++ tailWord_3451553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451553).length < 2 ^ (prefixWord ++ tailWord_3451553).sum := by decide
  have hdescent : baseEnd_3451553 < baseStart_3451553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451596 : List Nat := [2, 2, 1, 5, 1, 2, 2, 1, 1, 1, 5]
def baseStart_3451596 : Nat := 118140960795 + 3451596 * 2 ^ 59
def prefixEnd_3451596 : Nat := 4983230072969 + 3 ^ 40 * 3451596 * 2
def baseEnd_3451596 : Nat := 1772327773136182848476405

theorem tailTrace_3451596 : CollatzResearch.WordTrace tailWord_3451596 prefixEnd_3451596 1772327773136182848476405 := by
  unfold tailWord_3451596
  simp only [CollatzResearch.WordTrace]
  refine ⟨62945024201732326255279321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83926698935643101673705761 62945024201732326255279321)
  ·
    refine ⟨47208768151299244691459491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62945024201732326255279321 47208768151299244691459491)
    ·
      refine ⟨70813152226948867037189237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47208768151299244691459491 70813152226948867037189237)
      ·
        refine ⟨6638733021276456284736491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70813152226948867037189237 6638733021276456284736491)
        ·
          refine ⟨9958099531914684427104737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6638733021276456284736491 9958099531914684427104737)
          ·
            refine ⟨7468574648936013320328553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9958099531914684427104737 7468574648936013320328553)
            ·
              refine ⟨5601430986702009990246415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7468574648936013320328553 5601430986702009990246415)
              ·
                refine ⟨8402146480053014985369623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5601430986702009990246415 8402146480053014985369623)
                ·
                  refine ⟨12603219720079522478054435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8402146480053014985369623 12603219720079522478054435)
                  ·
                    refine ⟨18904829580119283717081653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12603219720079522478054435 18904829580119283717081653)
                    ·
                      refine ⟨1772327773136182848476405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18904829580119283717081653 1772327773136182848476405)
                      ·
                        rfl

theorem cell23_3451596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_3451596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3451596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3451596 prefixEnd_3451596 := by exact prefixLift 3451596
  have htrace : WordTrace (prefixWord ++ tailWord_3451596) baseStart_3451596 baseEnd_3451596 := by
    simpa [prefixWord, tailWord_3451596, baseEnd_3451596] using wordTrace_append hprefix tailTrace_3451596
  have hstable : (prefixWord ++ tailWord_3451596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451596).length < 2 ^ (prefixWord ++ tailWord_3451596).sum := by decide
  have hdescent : baseEnd_3451596 < baseStart_3451596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451669 : List Nat := [1, 3, 2, 1, 2, 2, 1, 1, 1, 6, 3]
def baseStart_3451669 : Nat := 118140960795 + 3451669 * 2 ^ 59
def prefixEnd_3451669 : Nat := 4983230072969 + 3 ^ 40 * 3451669 * 2
def baseEnd_3451669 : Nat := 1772365257223961062863569

theorem tailTrace_3451669 : CollatzResearch.WordTrace tailWord_3451669 prefixEnd_3451669 1772365257223961062863569 := by
  unfold tailWord_3451669
  simp only [CollatzResearch.WordTrace]
  refine ⟨125892710932200185977966061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83928473954800123985310707 125892710932200185977966061)
  ·
    refine ⟨47209766599575069741737273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125892710932200185977966061 47209766599575069741737273)
    ·
      refine ⟨35407324949681302306302955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47209766599575069741737273 35407324949681302306302955)
      ·
        refine ⟨53110987424521953459454433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35407324949681302306302955 53110987424521953459454433)
        ·
          refine ⟨39833240568391465094590825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53110987424521953459454433 39833240568391465094590825)
          ·
            refine ⟨29874930426293598820943119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39833240568391465094590825 29874930426293598820943119)
            ·
              refine ⟨44812395639440398231414679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29874930426293598820943119 44812395639440398231414679)
              ·
                refine ⟨67218593459160597347122019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44812395639440398231414679 67218593459160597347122019)
                ·
                  refine ⟨100827890188740896020683029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67218593459160597347122019 100827890188740896020683029)
                  ·
                    refine ⟨4726307352597229500969517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 100827890188740896020683029 4726307352597229500969517)
                    ·
                      refine ⟨1772365257223961062863569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4726307352597229500969517 1772365257223961062863569)
                      ·
                        rfl

theorem cell23_3451669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 6, 3].length) (baseStart_3451669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3451669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3451669 prefixEnd_3451669 := by exact prefixLift 3451669
  have htrace : WordTrace (prefixWord ++ tailWord_3451669) baseStart_3451669 baseEnd_3451669 := by
    simpa [prefixWord, tailWord_3451669, baseEnd_3451669] using wordTrace_append hprefix tailTrace_3451669
  have hstable : (prefixWord ++ tailWord_3451669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451669).length < 2 ^ (prefixWord ++ tailWord_3451669).sum := by decide
  have hdescent : baseEnd_3451669 < baseStart_3451669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451679 : List Nat := [1, 1, 2, 4, 2, 2, 1, 1, 1, 4, 4]
def baseStart_3451679 : Nat := 118140960795 + 3451679 * 2 ^ 59
def prefixEnd_3451679 : Nat := 4983230072969 + 3 ^ 40 * 3451679 * 2
def baseEnd_3451679 : Nat := 1772370392030506023738523

theorem tailTrace_3451679 : CollatzResearch.WordTrace tailWord_3451679 prefixEnd_3451679 1772370392030506023738523 := by
  unfold tailWord_3451679
  simp only [CollatzResearch.WordTrace]
  refine ⟨125893075662163957685830091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83928717108109305123886727 125893075662163957685830091)
  ·
    refine ⟨188839613493245936528745137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125893075662163957685830091 188839613493245936528745137)
    ·
      refine ⟨141629710119934452396558853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188839613493245936528745137 141629710119934452396558853)
      ·
        refine ⟨26555570647487709824354785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141629710119934452396558853 26555570647487709824354785)
        ·
          refine ⟨19916677985615782368266089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26555570647487709824354785 19916677985615782368266089)
          ·
            refine ⟨14937508489211836776199567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19916677985615782368266089 14937508489211836776199567)
            ·
              refine ⟨22406262733817755164299351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14937508489211836776199567 22406262733817755164299351)
              ·
                refine ⟨33609394100726632746449027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22406262733817755164299351 33609394100726632746449027)
                ·
                  refine ⟨50414091151089949119673541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33609394100726632746449027 50414091151089949119673541)
                  ·
                    refine ⟨9452642090829365459938789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50414091151089949119673541 9452642090829365459938789)
                    ·
                      refine ⟨1772370392030506023738523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9452642090829365459938789 1772370392030506023738523)
                      ·
                        rfl

theorem cell23_3451679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_3451679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3451679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3451679 prefixEnd_3451679 := by exact prefixLift 3451679
  have htrace : WordTrace (prefixWord ++ tailWord_3451679) baseStart_3451679 baseEnd_3451679 := by
    simpa [prefixWord, tailWord_3451679, baseEnd_3451679] using wordTrace_append hprefix tailTrace_3451679
  have hstable : (prefixWord ++ tailWord_3451679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451679).length < 2 ^ (prefixWord ++ tailWord_3451679).sum := by decide
  have hdescent : baseEnd_3451679 < baseStart_3451679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451719 : List Nat := [1, 1, 4, 1, 2, 1, 1, 3, 4, 5]
def baseStart_3451719 : Nat := 118140960795 + 3451719 * 2 ^ 59
def prefixEnd_3451719 : Nat := 4983230072969 + 3 ^ 40 * 3451719 * 2
def baseEnd_3451719 : Nat := 590796977085561955746113

theorem tailTrace_3451719 : CollatzResearch.WordTrace tailWord_3451719 prefixEnd_3451719 590796977085561955746113 := by
  unfold tailWord_3451719
  simp only [CollatzResearch.WordTrace]
  refine ⟨125894534582019044517286211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83929689721346029678190807 125894534582019044517286211)
  ·
    refine ⟨188841801873028566775929317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125894534582019044517286211 188841801873028566775929317)
    ·
      refine ⟨35407837851192856270486747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188841801873028566775929317 35407837851192856270486747)
      ·
        refine ⟨53111756776789284405730121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35407837851192856270486747 53111756776789284405730121)
        ·
          refine ⟨39833817582591963304297591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53111756776789284405730121 39833817582591963304297591)
          ·
            refine ⟨59750726373887944956446387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39833817582591963304297591 59750726373887944956446387)
            ·
              refine ⟨89626089560831917434669581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59750726373887944956446387 89626089560831917434669581)
              ·
                refine ⟨33609783585311969038001093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89626089560831917434669581 33609783585311969038001093)
                ·
                  refine ⟨6301834422245994194625205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33609783585311969038001093 6301834422245994194625205)
                  ·
                    refine ⟨590796977085561955746113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6301834422245994194625205 590796977085561955746113)
                    ·
                      rfl

theorem cell23_3451719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 4, 5].length) (baseStart_3451719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3451719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3451719 prefixEnd_3451719 := by exact prefixLift 3451719
  have htrace : WordTrace (prefixWord ++ tailWord_3451719) baseStart_3451719 baseEnd_3451719 := by
    simpa [prefixWord, tailWord_3451719, baseEnd_3451719] using wordTrace_append hprefix tailTrace_3451719
  have hstable : (prefixWord ++ tailWord_3451719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451719).length < 2 ^ (prefixWord ++ tailWord_3451719).sum := by decide
  have hdescent : baseEnd_3451719 < baseStart_3451719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451726 : List Nat := [4, 1, 1, 1, 1, 1, 1, 3, 1, 7, 2]
def baseStart_3451726 : Nat := 118140960795 + 3451726 * 2 ^ 59
def prefixEnd_3451726 : Nat := 4983230072969 + 3 ^ 40 * 3451726 * 2
def baseEnd_3451726 : Nat := 1772394525621267339850807

theorem tailTrace_3451726 : CollatzResearch.WordTrace tailWord_3451726 prefixEnd_3451726 1772394525621267339850807 := by
  unfold tailWord_3451726
  simp only [CollatzResearch.WordTrace]
  refine ⟨15736848736624210589098879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83929859928662456475194021 15736848736624210589098879)
  ·
    refine ⟨23605273104936315883648319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15736848736624210589098879 23605273104936315883648319)
    ·
      refine ⟨35407909657404473825472479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23605273104936315883648319 35407909657404473825472479)
      ·
        refine ⟨53111864486106710738208719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35407909657404473825472479 53111864486106710738208719)
        ·
          refine ⟨79667796729160066107313079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53111864486106710738208719 79667796729160066107313079)
          ·
            refine ⟨119501695093740099160969619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79667796729160066107313079 119501695093740099160969619)
            ·
              refine ⟨179252542640610148741454429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119501695093740099160969619 179252542640610148741454429)
              ·
                refine ⟨67219703490228805778045411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179252542640610148741454429 67219703490228805778045411)
                ·
                  refine ⟨100829555235343208667068117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67219703490228805778045411 100829555235343208667068117)
                  ·
                    refine ⟨2363192700828356453134409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 100829555235343208667068117 2363192700828356453134409)
                    ·
                      refine ⟨1772394525621267339850807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2363192700828356453134409 1772394525621267339850807)
                      ·
                        rfl

theorem cell23_3451726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 1, 7, 2].length) (baseStart_3451726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3451726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3451726 prefixEnd_3451726 := by exact prefixLift 3451726
  have htrace : WordTrace (prefixWord ++ tailWord_3451726) baseStart_3451726 baseEnd_3451726 := by
    simpa [prefixWord, tailWord_3451726, baseEnd_3451726] using wordTrace_append hprefix tailTrace_3451726
  have hstable : (prefixWord ++ tailWord_3451726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451726).length < 2 ^ (prefixWord ++ tailWord_3451726).sum := by decide
  have hdescent : baseEnd_3451726 < baseStart_3451726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451756 : List Nat := [2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 4]
def baseStart_3451756 : Nat := 118140960795 + 3451756 * 2 ^ 59
def prefixEnd_3451756 : Nat := 4983230072969 + 3 ^ 40 * 3451756 * 2
def baseEnd_3451756 : Nat := 1772409930040902222475669

theorem tailTrace_3451756 : CollatzResearch.WordTrace tailWord_3451756 prefixEnd_3451756 1772409930040902222475669 := by
  unfold tailWord_3451756
  simp only [CollatzResearch.WordTrace]
  refine ⟨62947942041442499918191561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83930589388589999890922081 62947942041442499918191561)
  ·
    refine ⟨47210956531081874938643671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62947942041442499918191561 47210956531081874938643671)
    ·
      refine ⟨70816434796622812407965507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47210956531081874938643671 70816434796622812407965507)
      ·
        refine ⟨106224652194934218611948261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70816434796622812407965507 106224652194934218611948261)
        ·
          refine ⟨19917122286550165989740299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106224652194934218611948261 19917122286550165989740299)
          ·
            refine ⟨29875683429825248984610449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19917122286550165989740299 29875683429825248984610449)
            ·
              refine ⟨22406762572368936738457837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29875683429825248984610449 22406762572368936738457837)
              ·
                refine ⟨8402535964638351276921689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22406762572368936738457837 8402535964638351276921689)
                ·
                  refine ⟨6301901973478763457691267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8402535964638351276921689 6301901973478763457691267)
                  ·
                    refine ⟨9452852960218145186536901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6301901973478763457691267 9452852960218145186536901)
                    ·
                      refine ⟨1772409930040902222475669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9452852960218145186536901 1772409930040902222475669)
                      ·
                        rfl

theorem cell23_3451756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 4].length) (baseStart_3451756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3451756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3451756 prefixEnd_3451756 := by exact prefixLift 3451756
  have htrace : WordTrace (prefixWord ++ tailWord_3451756) baseStart_3451756 baseEnd_3451756 := by
    simpa [prefixWord, tailWord_3451756, baseEnd_3451756] using wordTrace_append hprefix tailTrace_3451756
  have hstable : (prefixWord ++ tailWord_3451756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451756).length < 2 ^ (prefixWord ++ tailWord_3451756).sum := by decide
  have hdescent : baseEnd_3451756 < baseStart_3451756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451779 : List Nat := [1, 1, 1, 3, 4, 1, 1, 3, 8]
def baseStart_3451779 : Nat := 118140960795 + 3451779 * 2 ^ 59
def prefixEnd_3451779 : Nat := 4983230072969 + 3 ^ 40 * 3451779 * 2
def baseEnd_3451779 : Nat := 196935748899550625832007

theorem tailTrace_3451779 : CollatzResearch.WordTrace tailWord_3451779 prefixEnd_3451779 196935748899550625832007 := by
  unfold tailWord_3451779
  simp only [CollatzResearch.WordTrace]
  refine ⟨125896722961801674764470391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83931148641201116509646927 125896722961801674764470391)
  ·
    refine ⟨188845084442702512146705587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125896722961801674764470391 188845084442702512146705587)
    ·
      refine ⟨283267626664053768220058381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188845084442702512146705587 283267626664053768220058381)
      ·
        refine ⟨106225359999020163082521893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 283267626664053768220058381 106225359999020163082521893)
        ·
          refine ⟨19917254999816280577972855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106225359999020163082521893 19917254999816280577972855)
          ·
            refine ⟨29875882499724420866959283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19917254999816280577972855 29875882499724420866959283)
            ·
              refine ⟨44813823749586631300438925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29875882499724420866959283 44813823749586631300438925)
              ·
                refine ⟨16805183906094986737664597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44813823749586631300438925 16805183906094986737664597)
                ·
                  refine ⟨196935748899550625832007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16805183906094986737664597 196935748899550625832007)
                  ·
                    rfl

theorem cell23_3451779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 8].length) (baseStart_3451779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3451779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3451779 prefixEnd_3451779 := by exact prefixLift 3451779
  have htrace : WordTrace (prefixWord ++ tailWord_3451779) baseStart_3451779 baseEnd_3451779 := by
    simpa [prefixWord, tailWord_3451779, baseEnd_3451779] using wordTrace_append hprefix tailTrace_3451779
  have hstable : (prefixWord ++ tailWord_3451779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451779).length < 2 ^ (prefixWord ++ tailWord_3451779).sum := by decide
  have hdescent : baseEnd_3451779 < baseStart_3451779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451783 : List Nat := [1, 1, 4, 2, 3, 1, 3, 1, 3, 4]
def baseStart_3451783 : Nat := 118140960795 + 3451783 * 2 ^ 59
def prefixEnd_3451783 : Nat := 4983230072969 + 3 ^ 40 * 3451783 * 2
def baseEnd_3451783 : Nat := 590807931339524538946015

theorem tailTrace_3451783 : CollatzResearch.WordTrace tailWord_3451783 prefixEnd_3451783 590807931339524538946015 := by
  unfold tailWord_3451783
  simp only [CollatzResearch.WordTrace]
  refine ⟨125896868853787183447616003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83931245902524788965077335 125896868853787183447616003)
  ·
    refine ⟨188845303280680775171424005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125896868853787183447616003 188845303280680775171424005)
    ·
      refine ⟨35408494365127645344642001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188845303280680775171424005 35408494365127645344642001)
      ·
        refine ⟨26556370773845734008481501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35408494365127645344642001 26556370773845734008481501)
        ·
          refine ⟨9958639040192150253180563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26556370773845734008481501 9958639040192150253180563)
          ·
            refine ⟨14937958560288225379770845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9958639040192150253180563 14937958560288225379770845)
            ·
              refine ⟨5601734460108084517414067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14937958560288225379770845 5601734460108084517414067)
              ·
                refine ⟨8402601690162126776121101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5601734460108084517414067 8402601690162126776121101)
                ·
                  refine ⟨3150975633810797541045413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8402601690162126776121101 3150975633810797541045413)
                  ·
                    refine ⟨590807931339524538946015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3150975633810797541045413 590807931339524538946015)
                    ·
                      rfl

theorem cell23_3451783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 3, 4].length) (baseStart_3451783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3451783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3451783 prefixEnd_3451783 := by exact prefixLift 3451783
  have htrace : WordTrace (prefixWord ++ tailWord_3451783) baseStart_3451783 baseEnd_3451783 := by
    simpa [prefixWord, tailWord_3451783, baseEnd_3451783] using wordTrace_append hprefix tailTrace_3451783
  have hstable : (prefixWord ++ tailWord_3451783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451783).length < 2 ^ (prefixWord ++ tailWord_3451783).sum := by decide
  have hdescent : baseEnd_3451783 < baseStart_3451783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451810 : List Nat := [3, 3, 1, 2, 2, 2, 2, 1, 2, 2, 3]
def baseStart_3451810 : Nat := 118140960795 + 3451810 * 2 ^ 59
def prefixEnd_3451810 : Nat := 4983230072969 + 3 ^ 40 * 3451810 * 2
def baseEnd_3451810 : Nat := 1772437657996245011200421

theorem tailTrace_3451810 : CollatzResearch.WordTrace tailWord_3451810 prefixEnd_3451810 1772437657996245011200421 := by
  unfold tailWord_3451810
  simp only [CollatzResearch.WordTrace]
  refine ⟨31474463406172341764712221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83931902416459578039232589 31474463406172341764712221)
  ·
    refine ⟨11802923777314628161767083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31474463406172341764712221 11802923777314628161767083)
    ·
      refine ⟨17704385665971942242650625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11802923777314628161767083 17704385665971942242650625)
      ·
        refine ⟨13278289249478956681987969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17704385665971942242650625 13278289249478956681987969)
        ·
          refine ⟨9958716937109217511490977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13278289249478956681987969 9958716937109217511490977)
          ·
            refine ⟨7469037702831913133618233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9958716937109217511490977 7469037702831913133618233)
            ·
              refine ⟨5601778277123934850213675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7469037702831913133618233 5601778277123934850213675)
              ·
                refine ⟨8402667415685902275320513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5601778277123934850213675 8402667415685902275320513)
                ·
                  refine ⟨6302000561764426706490385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8402667415685902275320513 6302000561764426706490385)
                  ·
                    refine ⟨4726500421323320029867789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6302000561764426706490385 4726500421323320029867789)
                    ·
                      refine ⟨1772437657996245011200421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4726500421323320029867789 1772437657996245011200421)
                      ·
                        rfl

theorem cell23_3451810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_3451810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3451810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3451810 prefixEnd_3451810 := by exact prefixLift 3451810
  have htrace : WordTrace (prefixWord ++ tailWord_3451810) baseStart_3451810 baseEnd_3451810 := by
    simpa [prefixWord, tailWord_3451810, baseEnd_3451810] using wordTrace_append hprefix tailTrace_3451810
  have hstable : (prefixWord ++ tailWord_3451810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451810).length < 2 ^ (prefixWord ++ tailWord_3451810).sum := by decide
  have hdescent : baseEnd_3451810 < baseStart_3451810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451856 : List Nat := [2, 1, 1, 1, 1, 2, 3, 2, 6, 4]
def baseStart_3451856 : Nat := 118140960795 + 3451856 * 2 ^ 59
def prefixEnd_3451856 : Nat := 4983230072969 + 3 ^ 40 * 3451856 * 2
def baseEnd_3451856 : Nat := 590820426035450610408403

theorem tailTrace_3451856 : CollatzResearch.WordTrace tailWord_3451856 prefixEnd_3451856 590820426035450610408403 := by
  unfold tailWord_3451856
  simp only [CollatzResearch.WordTrace]
  refine ⟨62949765691261358457511711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83933020921681811276682281 62949765691261358457511711)
  ·
    refine ⟨94424648536892037686267567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62949765691261358457511711 94424648536892037686267567)
    ·
      refine ⟨141636972805338056529401351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94424648536892037686267567 141636972805338056529401351)
      ·
        refine ⟨212455459208007084794102027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141636972805338056529401351 212455459208007084794102027)
        ·
          refine ⟨318683188812010627191153041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212455459208007084794102027 318683188812010627191153041)
          ·
            refine ⟨239012391609007970393364781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318683188812010627191153041 239012391609007970393364781)
            ·
              refine ⟨89629646853377988897511793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 239012391609007970393364781 89629646853377988897511793)
              ·
                refine ⟨67222235140033491673133845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89629646853377988897511793 67222235140033491673133845)
                ·
                  refine ⟨3151042272189069922178149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 67222235140033491673133845 3151042272189069922178149)
                  ·
                    refine ⟨590820426035450610408403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3151042272189069922178149 590820426035450610408403)
                    ·
                      rfl

theorem cell23_3451856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 6, 4].length) (baseStart_3451856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3451856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3451856 prefixEnd_3451856 := by exact prefixLift 3451856
  have htrace : WordTrace (prefixWord ++ tailWord_3451856) baseStart_3451856 baseEnd_3451856 := by
    simpa [prefixWord, tailWord_3451856, baseEnd_3451856] using wordTrace_append hprefix tailTrace_3451856
  have hstable : (prefixWord ++ tailWord_3451856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451856).length < 2 ^ (prefixWord ++ tailWord_3451856).sum := by decide
  have hdescent : baseEnd_3451856 < baseStart_3451856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451874 : List Nat := [3, 3, 3, 1, 1, 1, 1, 5, 1, 1, 3]
def baseStart_3451874 : Nat := 118140960795 + 3451874 * 2 ^ 59
def prefixEnd_3451874 : Nat := 4983230072969 + 3 ^ 40 * 3451874 * 2
def baseEnd_3451874 : Nat := 1772470520758132760800127

theorem tailTrace_3451874 : CollatzResearch.WordTrace tailWord_3451874 prefixEnd_3451874 1772470520758132760800127 := by
  unfold tailWord_3451874
  simp only [CollatzResearch.WordTrace]
  refine ⟨31475046974114376497294669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83933458597638337326119117 31475046974114376497294669)
  ·
    refine ⟨11803142615292891186485501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31475046974114376497294669 11803142615292891186485501)
    ·
      refine ⟨4426178480734834194932063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11803142615292891186485501 4426178480734834194932063)
      ·
        refine ⟨6639267721102251292398095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4426178480734834194932063 6639267721102251292398095)
        ·
          refine ⟨9958901581653376938597143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6639267721102251292398095 9958901581653376938597143)
          ·
            refine ⟨14938352372480065407895715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9958901581653376938597143 14938352372480065407895715)
            ·
              refine ⟨22407528558720098111843573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14938352372480065407895715 22407528558720098111843573)
              ·
                refine ⟨2100705802380009197985335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22407528558720098111843573 2100705802380009197985335)
                ·
                  refine ⟨3151058703570013796978003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2100705802380009197985335 3151058703570013796978003)
                  ·
                    refine ⟨4726588055355020695467005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3151058703570013796978003 4726588055355020695467005)
                    ·
                      refine ⟨1772470520758132760800127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4726588055355020695467005 1772470520758132760800127)
                      ·
                        rfl

theorem cell23_3451874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_3451874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3451874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3451874 prefixEnd_3451874 := by exact prefixLift 3451874
  have htrace : WordTrace (prefixWord ++ tailWord_3451874) baseStart_3451874 baseEnd_3451874 := by
    simpa [prefixWord, tailWord_3451874, baseEnd_3451874] using wordTrace_append hprefix tailTrace_3451874
  have hstable : (prefixWord ++ tailWord_3451874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451874).length < 2 ^ (prefixWord ++ tailWord_3451874).sum := by decide
  have hdescent : baseEnd_3451874 < baseStart_3451874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451876 : List Nat := [2, 3, 1, 1, 1, 1, 2, 3, 3, 2, 4]
def baseStart_3451876 : Nat := 118140960795 + 3451876 * 2 ^ 59
def prefixEnd_3451876 : Nat := 4983230072969 + 3 ^ 40 * 3451876 * 2
def baseEnd_3451876 : Nat := 1772471547719441752975117

theorem tailTrace_3451876 : CollatzResearch.WordTrace tailWord_3451876 prefixEnd_3451876 1772471547719441752975117 := by
  unfold tailWord_3451876
  simp only [CollatzResearch.WordTrace]
  refine ⟨62950130421225130165375741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83933507228300173553834321 62950130421225130165375741)
  ·
    refine ⟨23606298907959423812015903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62950130421225130165375741 23606298907959423812015903)
    ·
      refine ⟨35409448361939135718023855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23606298907959423812015903 35409448361939135718023855)
      ·
        refine ⟨53114172542908703577035783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35409448361939135718023855 53114172542908703577035783)
        ·
          refine ⟨79671258814363055365553675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53114172542908703577035783 79671258814363055365553675)
          ·
            refine ⟨119506888221544583048330513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79671258814363055365553675 119506888221544583048330513)
            ·
              refine ⟨89630166166158437286247885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119506888221544583048330513 89630166166158437286247885)
              ·
                refine ⟨33611312312309413982342957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89630166166158437286247885 33611312312309413982342957)
                ·
                  refine ⟨12604242117116030243378609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33611312312309413982342957 12604242117116030243378609)
                  ·
                    refine ⟨9453181587837022682533957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12604242117116030243378609 9453181587837022682533957)
                    ·
                      refine ⟨1772471547719441752975117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9453181587837022682533957 1772471547719441752975117)
                      ·
                        rfl

theorem cell23_3451876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_3451876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3451876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3451876 prefixEnd_3451876 := by exact prefixLift 3451876
  have htrace : WordTrace (prefixWord ++ tailWord_3451876) baseStart_3451876 baseEnd_3451876 := by
    simpa [prefixWord, tailWord_3451876, baseEnd_3451876] using wordTrace_append hprefix tailTrace_3451876
  have hstable : (prefixWord ++ tailWord_3451876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451876).length < 2 ^ (prefixWord ++ tailWord_3451876).sum := by decide
  have hdescent : baseEnd_3451876 < baseStart_3451876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451880 : List Nat := [2, 1, 4, 1, 1, 1, 6, 1, 1, 1, 4]
def baseStart_3451880 : Nat := 118140960795 + 3451880 * 2 ^ 59
def prefixEnd_3451880 : Nat := 4983230072969 + 3 ^ 40 * 3451880 * 2
def baseEnd_3451880 : Nat := 1772473601642059737325099

theorem tailTrace_3451880 : CollatzResearch.WordTrace tailWord_3451880 prefixEnd_3451880 1772473601642059737325099 := by
  unfold tailWord_3451880
  simp only [CollatzResearch.WordTrace]
  refine ⟨62950203367217884506948547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83933604489623846009264729 62950203367217884506948547)
  ·
    refine ⟨94425305050826826760422821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62950203367217884506948547 94425305050826826760422821)
    ·
      refine ⟨17704744697030030017579279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94425305050826826760422821 17704744697030030017579279)
      ·
        refine ⟨26557117045545045026368919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17704744697030030017579279 26557117045545045026368919)
        ·
          refine ⟨39835675568317567539553379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26557117045545045026368919 39835675568317567539553379)
          ·
            refine ⟨59753513352476351309330069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39835675568317567539553379 59753513352476351309330069)
            ·
              refine ⟨2800945938397328967624847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 59753513352476351309330069 2800945938397328967624847)
              ·
                refine ⟨4201418907595993451437271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2800945938397328967624847 4201418907595993451437271)
                ·
                  refine ⟨6302128361393990177155907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4201418907595993451437271 6302128361393990177155907)
                  ·
                    refine ⟨9453192542090985265733861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6302128361393990177155907 9453192542090985265733861)
                    ·
                      refine ⟨1772473601642059737325099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9453192542090985265733861 1772473601642059737325099)
                      ·
                        rfl

theorem cell23_3451880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 1, 1, 1, 4].length) (baseStart_3451880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3451880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3451880 prefixEnd_3451880 := by exact prefixLift 3451880
  have htrace : WordTrace (prefixWord ++ tailWord_3451880) baseStart_3451880 baseEnd_3451880 := by
    simpa [prefixWord, tailWord_3451880, baseEnd_3451880] using wordTrace_append hprefix tailTrace_3451880
  have hstable : (prefixWord ++ tailWord_3451880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451880).length < 2 ^ (prefixWord ++ tailWord_3451880).sum := by decide
  have hdescent : baseEnd_3451880 < baseStart_3451880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451897 : List Nat := [1, 2, 1, 3, 1, 3, 1, 6, 1, 2, 2]
def baseStart_3451897 : Nat := 118140960795 + 3451897 * 2 ^ 59
def prefixEnd_3451897 : Nat := 4983230072969 + 3 ^ 40 * 3451897 * 2
def baseEnd_3451897 : Nat := 1772482330813186170812521

theorem tailTrace_3451897 : CollatzResearch.WordTrace tailWord_3451897 prefixEnd_3451897 1772482330813186170812521 := by
  unfold tailWord_3451897
  simp only [CollatzResearch.WordTrace]
  refine ⟨125901026775374180917265945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83934017850249453944843963 125901026775374180917265945)
  ·
    refine ⟨94425770081530635687949459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125901026775374180917265945 94425770081530635687949459)
    ·
      refine ⟨141638655122295953531924189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94425770081530635687949459 141638655122295953531924189)
      ·
        refine ⟨53114495670860982574471571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141638655122295953531924189 53114495670860982574471571)
        ·
          refine ⟨79671743506291473861707357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53114495670860982574471571 79671743506291473861707357)
          ·
            refine ⟨29876903814859302698140259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79671743506291473861707357 29876903814859302698140259)
            ·
              refine ⟨44815355722288954047210389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29876903814859302698140259 44815355722288954047210389)
              ·
                refine ⟨2100719799482294720962987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44815355722288954047210389 2100719799482294720962987)
                ·
                  refine ⟨3151079699223442081444481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2100719799482294720962987 3151079699223442081444481)
                  ·
                    refine ⟨2363309774417581561083361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3151079699223442081444481 2363309774417581561083361)
                    ·
                      refine ⟨1772482330813186170812521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2363309774417581561083361 1772482330813186170812521)
                      ·
                        rfl

theorem cell23_3451897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 6, 1, 2, 2].length) (baseStart_3451897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3451897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3451897 prefixEnd_3451897 := by exact prefixLift 3451897
  have htrace : WordTrace (prefixWord ++ tailWord_3451897) baseStart_3451897 baseEnd_3451897 := by
    simpa [prefixWord, tailWord_3451897, baseEnd_3451897] using wordTrace_append hprefix tailTrace_3451897
  have hstable : (prefixWord ++ tailWord_3451897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451897).length < 2 ^ (prefixWord ++ tailWord_3451897).sum := by decide
  have hdescent : baseEnd_3451897 < baseStart_3451897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451964 : List Nat := [2, 2, 2, 2, 2, 4, 2, 1, 2, 1, 3]
def baseStart_3451964 : Nat := 118140960795 + 3451964 * 2 ^ 59
def prefixEnd_3451964 : Nat := 4983230072969 + 3 ^ 40 * 3451964 * 2
def baseEnd_3451964 : Nat := 1772516734017037408674713

theorem tailTrace_3451964 : CollatzResearch.WordTrace tailWord_3451964 prefixEnd_3451964 1772516734017037408674713 := by
  unfold tailWord_3451964
  simp only [CollatzResearch.WordTrace]
  refine ⟨62951735233065725679977473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83935646977420967573303297 62951735233065725679977473)
  ·
    refine ⟨47213801424799294259983105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62951735233065725679977473 47213801424799294259983105)
    ·
      refine ⟨35410351068599470694987329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47213801424799294259983105 35410351068599470694987329)
      ·
        refine ⟨26557763301449603021240497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35410351068599470694987329 26557763301449603021240497)
        ·
          refine ⟨19918322476087202265930373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26557763301449603021240497 19918322476087202265930373)
          ·
            refine ⟨3734685464266350424861945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19918322476087202265930373 3734685464266350424861945)
            ·
              refine ⟨2801014098199762818646459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3734685464266350424861945 2801014098199762818646459)
              ·
                refine ⟨4201521147299644227969689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2801014098199762818646459 4201521147299644227969689)
                ·
                  refine ⟨3151140860474733170977267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4201521147299644227969689 3151140860474733170977267)
                  ·
                    refine ⟨4726711290712099756465901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3151140860474733170977267 4726711290712099756465901)
                    ·
                      refine ⟨1772516734017037408674713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4726711290712099756465901 1772516734017037408674713)
                      ·
                        rfl

theorem cell23_3451964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 1, 2, 1, 3].length) (baseStart_3451964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3451964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3451964 prefixEnd_3451964 := by exact prefixLift 3451964
  have htrace : WordTrace (prefixWord ++ tailWord_3451964) baseStart_3451964 baseEnd_3451964 := by
    simpa [prefixWord, tailWord_3451964, baseEnd_3451964] using wordTrace_append hprefix tailTrace_3451964
  have hstable : (prefixWord ++ tailWord_3451964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451964).length < 2 ^ (prefixWord ++ tailWord_3451964).sum := by decide
  have hdescent : baseEnd_3451964 < baseStart_3451964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451974 : List Nat := [6, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2]
def baseStart_3451974 : Nat := 118140960795 + 3451974 * 2 ^ 59
def prefixEnd_3451974 : Nat := 4983230072969 + 3 ^ 40 * 3451974 * 2
def baseEnd_3451974 : Nat := 1772521868823582369549667

theorem tailTrace_3451974 : CollatzResearch.WordTrace tailWord_3451974 prefixEnd_3451974 1772521868823582369549667 := by
  unfold tailWord_3451974
  simp only [CollatzResearch.WordTrace]
  refine ⟨3934494849877975720869343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 83935890130730148711879317 3934494849877975720869343)
  ·
    refine ⟨5901742274816963581304015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3934494849877975720869343 5901742274816963581304015)
    ·
      refine ⟨8852613412225445371956023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5901742274816963581304015 8852613412225445371956023)
      ·
        refine ⟨13278920118338168057934035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8852613412225445371956023 13278920118338168057934035)
        ·
          refine ⟨19918380177507252086901053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13278920118338168057934035 19918380177507252086901053)
          ·
            refine ⟨7469392566565219532587895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19918380177507252086901053 7469392566565219532587895)
            ·
              refine ⟨11204088849847829298881843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7469392566565219532587895 11204088849847829298881843)
              ·
                refine ⟨16806133274771743948322765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11204088849847829298881843 16806133274771743948322765)
                ·
                  refine ⟨6302299978039403980621037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16806133274771743948322765 6302299978039403980621037)
                  ·
                    refine ⟨2363362491764776492732889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6302299978039403980621037 2363362491764776492732889)
                    ·
                      refine ⟨1772521868823582369549667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2363362491764776492732889 1772521868823582369549667)
                      ·
                        rfl

theorem cell23_3451974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_3451974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3451974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3451974 prefixEnd_3451974 := by exact prefixLift 3451974
  have htrace : WordTrace (prefixWord ++ tailWord_3451974) baseStart_3451974 baseEnd_3451974 := by
    simpa [prefixWord, tailWord_3451974, baseEnd_3451974] using wordTrace_append hprefix tailTrace_3451974
  have hstable : (prefixWord ++ tailWord_3451974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451974).length < 2 ^ (prefixWord ++ tailWord_3451974).sum := by decide
  have hdescent : baseEnd_3451974 < baseStart_3451974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3451976 : List Nat := [2, 1, 3, 1, 1, 1, 4, 1, 9]
def baseStart_3451976 : Nat := 118140960795 + 3451976 * 2 ^ 59
def prefixEnd_3451976 : Nat := 4983230072969 + 3 ^ 40 * 3451976 * 2
def baseEnd_3451976 : Nat := 196946988420543484636073

theorem tailTrace_3451976 : CollatzResearch.WordTrace tailWord_3451976 prefixEnd_3451976 196946988420543484636073 := by
  unfold tailWord_3451976
  simp only [CollatzResearch.WordTrace]
  refine ⟨62951954071043988704695891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83935938761391984939594521 62951954071043988704695891)
  ·
    refine ⟨94427931106565983057043837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62951954071043988704695891 94427931106565983057043837)
    ·
      refine ⟨35410474164962243646391439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94427931106565983057043837 35410474164962243646391439)
      ·
        refine ⟨53115711247443365469587159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35410474164962243646391439 53115711247443365469587159)
        ·
          refine ⟨79673566871165048204380739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53115711247443365469587159 79673566871165048204380739)
          ·
            refine ⟨119510350306747572306571109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79673566871165048204380739 119510350306747572306571109)
            ·
              refine ⟨22408190682515169807482083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119510350306747572306571109 22408190682515169807482083)
              ·
                refine ⟨33612286023772754711223125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22408190682515169807482083 33612286023772754711223125)
                ·
                  refine ⟨196946988420543484636073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 33612286023772754711223125 196946988420543484636073)
                  ·
                    rfl

theorem cell23_3451976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 9].length) (baseStart_3451976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3451976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3451976 prefixEnd_3451976 := by exact prefixLift 3451976
  have htrace : WordTrace (prefixWord ++ tailWord_3451976) baseStart_3451976 baseEnd_3451976 := by
    simpa [prefixWord, tailWord_3451976, baseEnd_3451976] using wordTrace_append hprefix tailTrace_3451976
  have hstable : (prefixWord ++ tailWord_3451976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3451976).length < 2 ^ (prefixWord ++ tailWord_3451976).sum := by decide
  have hdescent : baseEnd_3451976 < baseStart_3451976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3451976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452003 : List Nat := [1, 1, 1, 5, 1, 1, 1, 4, 2, 3, 3]
def baseStart_3452003 : Nat := 118140960795 + 3452003 * 2 ^ 59
def prefixEnd_3452003 : Nat := 4983230072969 + 3 ^ 40 * 3452003 * 2
def baseEnd_3452003 : Nat := 1772536759762562756087033

theorem tailTrace_3452003 : CollatzResearch.WordTrace tailWord_3452003 prefixEnd_3452003 1772536759762562756087033 := by
  unfold tailWord_3452003
  simp only [CollatzResearch.WordTrace]
  refine ⟨125904892912990161020624663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83936595275326774013749775 125904892912990161020624663)
  ·
    refine ⟨188857339369485241530936995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125904892912990161020624663 188857339369485241530936995)
    ·
      refine ⟨283286009054227862296405493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188857339369485241530936995 283286009054227862296405493)
      ·
        refine ⟨26558063348833862090288015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 283286009054227862296405493 26558063348833862090288015)
        ·
          refine ⟨39837095023250793135432023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26558063348833862090288015 39837095023250793135432023)
          ·
            refine ⟨59755642534876189703148035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39837095023250793135432023 59755642534876189703148035)
            ·
              refine ⟨89633463802314284554722053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59755642534876189703148035 89633463802314284554722053)
              ·
                refine ⟨16806274462933928354010385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89633463802314284554722053 16806274462933928354010385)
                ·
                  refine ⟨12604705847200446265507789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16806274462933928354010385 12604705847200446265507789)
                  ·
                    refine ⟨4726764692700167349565421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12604705847200446265507789 4726764692700167349565421)
                    ·
                      refine ⟨1772536759762562756087033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4726764692700167349565421 1772536759762562756087033)
                      ·
                        rfl

theorem cell23_3452003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_3452003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452003 prefixEnd_3452003 := by exact prefixLift 3452003
  have htrace : WordTrace (prefixWord ++ tailWord_3452003) baseStart_3452003 baseEnd_3452003 := by
    simpa [prefixWord, tailWord_3452003, baseEnd_3452003] using wordTrace_append hprefix tailTrace_3452003
  have hstable : (prefixWord ++ tailWord_3452003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452003).length < 2 ^ (prefixWord ++ tailWord_3452003).sum := by decide
  have hdescent : baseEnd_3452003 < baseStart_3452003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452040 : List Nat := [2, 1, 3, 4, 2, 1, 1, 1, 1, 7]
def baseStart_3452040 : Nat := 118140960795 + 3452040 * 2 ^ 59
def prefixEnd_3452040 : Nat := 4983230072969 + 3 ^ 40 * 3452040 * 2
def baseEnd_3452040 : Nat := 590851919515593037108121

theorem tailTrace_3452040 : CollatzResearch.WordTrace tailWord_3452040 prefixEnd_3452040 590851919515593037108121 := by
  unfold tailWord_3452040
  simp only [CollatzResearch.WordTrace]
  refine ⟨62953121206928058169860787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83937494942570744226481049 62953121206928058169860787)
  ·
    refine ⟨94429681810392087254791181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62953121206928058169860787 94429681810392087254791181)
    ·
      refine ⟨35411130678897032720546693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94429681810392087254791181 35411130678897032720546693)
      ·
        refine ⟨6639587002293193635102505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35411130678897032720546693 6639587002293193635102505)
        ·
          refine ⟨4979690251719895226326879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6639587002293193635102505 4979690251719895226326879)
          ·
            refine ⟨7469535377579842839490319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4979690251719895226326879 7469535377579842839490319)
            ·
              refine ⟨11204303066369764259235479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7469535377579842839490319 11204303066369764259235479)
              ·
                refine ⟨16806454599554646388853219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11204303066369764259235479 16806454599554646388853219)
                ·
                  refine ⟨25209681899331969583279829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16806454599554646388853219 25209681899331969583279829)
                  ·
                    refine ⟨590851919515593037108121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25209681899331969583279829 590851919515593037108121)
                    ·
                      rfl

theorem cell23_3452040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 1, 7].length) (baseStart_3452040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452040 prefixEnd_3452040 := by exact prefixLift 3452040
  have htrace : WordTrace (prefixWord ++ tailWord_3452040) baseStart_3452040 baseEnd_3452040 := by
    simpa [prefixWord, tailWord_3452040, baseEnd_3452040] using wordTrace_append hprefix tailTrace_3452040
  have hstable : (prefixWord ++ tailWord_3452040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452040).length < 2 ^ (prefixWord ++ tailWord_3452040).sum := by decide
  have hdescent : baseEnd_3452040 < baseStart_3452040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452083 : List Nat := [1, 1, 1, 2, 3, 2, 2, 5, 6]
def baseStart_3452083 : Nat := 118140960795 + 3452083 * 2 ^ 59
def prefixEnd_3452083 : Nat := 4983230072969 + 3 ^ 40 * 3452083 * 2
def baseEnd_3452083 : Nat := 196953093134991382565185

theorem tailTrace_3452083 : CollatzResearch.WordTrace tailWord_3452083 prefixEnd_3452083 196953093134991382565185 := by
  unfold tailWord_3452083
  simp only [CollatzResearch.WordTrace]
  refine ⟨125907810752700334683536903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83938540501800223122357935 125907810752700334683536903)
  ·
    refine ⟨188861716129050502025305355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125907810752700334683536903 188861716129050502025305355)
    ·
      refine ⟨283292574193575753037958033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188861716129050502025305355 283292574193575753037958033)
      ·
        refine ⟨212469430645181814778468525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283292574193575753037958033 212469430645181814778468525)
        ·
          refine ⟨79676036491943180541925697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212469430645181814778468525 79676036491943180541925697)
          ·
            refine ⟨59757027368957385406444273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79676036491943180541925697 59757027368957385406444273)
            ·
              refine ⟨44817770526718039054833205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59757027368957385406444273 44817770526718039054833205)
              ·
                refine ⟨4201665986879816161390613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44817770526718039054833205 4201665986879816161390613)
                ·
                  refine ⟨196953093134991382565185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4201665986879816161390613 196953093134991382565185)
                  ·
                    rfl

theorem cell23_3452083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 5, 6].length) (baseStart_3452083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452083 prefixEnd_3452083 := by exact prefixLift 3452083
  have htrace : WordTrace (prefixWord ++ tailWord_3452083) baseStart_3452083 baseEnd_3452083 := by
    simpa [prefixWord, tailWord_3452083, baseEnd_3452083] using wordTrace_append hprefix tailTrace_3452083
  have hstable : (prefixWord ++ tailWord_3452083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452083).length < 2 ^ (prefixWord ++ tailWord_3452083).sum := by decide
  have hdescent : baseEnd_3452083 < baseStart_3452083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452097 : List Nat := [1, 2, 6, 1, 1, 1, 2, 1, 1, 4, 3]
def baseStart_3452097 : Nat := 118140960795 + 3452097 * 2 ^ 59
def prefixEnd_3452097 : Nat := 4983230072969 + 3 ^ 40 * 3452097 * 2
def baseEnd_3452097 : Nat := 1772585026944085388311601

theorem tailTrace_3452097 : CollatzResearch.WordTrace tailWord_3452097 prefixEnd_3452097 1772585026944085388311601 := by
  unfold tailWord_3452097
  simp only [CollatzResearch.WordTrace]
  refine ⟨125908321374649615074546545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83938880916433076716364363 125908321374649615074546545)
  ·
    refine ⟨94431241030987211305909909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125908321374649615074546545 94431241030987211305909909)
    ·
      refine ⟨4426464423327525529964527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 94431241030987211305909909 4426464423327525529964527)
      ·
        refine ⟨6639696634991288294946791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4426464423327525529964527 6639696634991288294946791)
        ·
          refine ⟨9959544952486932442420187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6639696634991288294946791 9959544952486932442420187)
          ·
            refine ⟨14939317428730398663630281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9959544952486932442420187 14939317428730398663630281)
            ·
              refine ⟨11204488071547798997722711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14939317428730398663630281 11204488071547798997722711)
              ·
                refine ⟨16806732107321698496584067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11204488071547798997722711 16806732107321698496584067)
                ·
                  refine ⟨25210098160982547744876101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16806732107321698496584067 25210098160982547744876101)
                  ·
                    refine ⟨4726893405184227702164269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25210098160982547744876101 4726893405184227702164269)
                    ·
                      refine ⟨1772585026944085388311601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4726893405184227702164269 1772585026944085388311601)
                      ·
                        rfl

theorem cell23_3452097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_3452097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452097 prefixEnd_3452097 := by exact prefixLift 3452097
  have htrace : WordTrace (prefixWord ++ tailWord_3452097) baseStart_3452097 baseEnd_3452097 := by
    simpa [prefixWord, tailWord_3452097, baseEnd_3452097] using wordTrace_append hprefix tailTrace_3452097
  have hstable : (prefixWord ++ tailWord_3452097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452097).length < 2 ^ (prefixWord ++ tailWord_3452097).sum := by decide
  have hdescent : baseEnd_3452097 < baseStart_3452097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452113 : List Nat := [1, 2, 2, 1, 2, 2, 1, 2, 5, 5]
def baseStart_3452113 : Nat := 118140960795 + 3452113 * 2 ^ 59
def prefixEnd_3452113 : Nat := 4983230072969 + 3 ^ 40 * 3452113 * 2
def baseEnd_3452113 : Nat := 590864414211519108570509

theorem tailTrace_3452113 : CollatzResearch.WordTrace tailWord_3452113 prefixEnd_3452113 590864414211519108570509 := by
  unfold tailWord_3452113
  simp only [CollatzResearch.WordTrace]
  refine ⟨125908904942591649807128993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83939269961727766538085995 125908904942591649807128993)
  ·
    refine ⟨94431678706943737355346745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125908904942591649807128993 94431678706943737355346745)
    ·
      refine ⟨70823759030207803016510059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94431678706943737355346745 70823759030207803016510059)
      ·
        refine ⟨106235638545311704524765089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70823759030207803016510059 106235638545311704524765089)
        ·
          refine ⟨79676728908983778393573817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106235638545311704524765089 79676728908983778393573817)
          ·
            refine ⟨59757546681737833795180363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79676728908983778393573817 59757546681737833795180363)
            ·
              refine ⟨89636320022606750692770545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59757546681737833795180363 89636320022606750692770545)
              ·
                refine ⟨67227240016955063019577909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89636320022606750692770545 67227240016955063019577909)
                ·
                  refine ⟨6302553751589537158085429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67227240016955063019577909 6302553751589537158085429)
                  ·
                    refine ⟨590864414211519108570509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6302553751589537158085429 590864414211519108570509)
                    ·
                      rfl

theorem cell23_3452113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 5, 5].length) (baseStart_3452113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452113 prefixEnd_3452113 := by exact prefixLift 3452113
  have htrace : WordTrace (prefixWord ++ tailWord_3452113) baseStart_3452113 baseEnd_3452113 := by
    simpa [prefixWord, tailWord_3452113, baseEnd_3452113] using wordTrace_append hprefix tailTrace_3452113
  have hstable : (prefixWord ++ tailWord_3452113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452113).length < 2 ^ (prefixWord ++ tailWord_3452113).sum := by decide
  have hdescent : baseEnd_3452113 < baseStart_3452113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452127 : List Nat := [1, 1, 2, 3, 2, 1, 5, 1, 3, 1, 3]
def baseStart_3452127 : Nat := 118140960795 + 3452127 * 2 ^ 59
def prefixEnd_3452127 : Nat := 4983230072969 + 3 ^ 40 * 3452127 * 2
def baseEnd_3452127 : Nat := 1772600431363720270936463

theorem tailTrace_3452127 : CollatzResearch.WordTrace tailWord_3452127 prefixEnd_3452127 1772600431363720270936463 := by
  unfold tailWord_3452127
  simp only [CollatzResearch.WordTrace]
  refine ⟨125909415564540930198138635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83939610376360620132092423 125909415564540930198138635)
  ·
    refine ⟨188864123346811395297207953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125909415564540930198138635 188864123346811395297207953)
    ·
      refine ⟨141648092510108546472905965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188864123346811395297207953 141648092510108546472905965)
      ·
        refine ⟨53118034691290704927339737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141648092510108546472905965 53118034691290704927339737)
        ·
          refine ⟨39838526018468028695504803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53118034691290704927339737 39838526018468028695504803)
          ·
            refine ⟨59757789027702043043257205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39838526018468028695504803 59757789027702043043257205)
            ·
              refine ⟨5602292721347066535305363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59757789027702043043257205 5602292721347066535305363)
              ·
                refine ⟨8403439082020599802958045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5602292721347066535305363 8403439082020599802958045)
                ·
                  refine ⟨3151289655757724926109267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8403439082020599802958045 3151289655757724926109267)
                  ·
                    refine ⟨4726934483636587389163901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3151289655757724926109267 4726934483636587389163901)
                    ·
                      refine ⟨1772600431363720270936463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4726934483636587389163901 1772600431363720270936463)
                      ·
                        rfl

theorem cell23_3452127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 3, 1, 3].length) (baseStart_3452127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452127 prefixEnd_3452127 := by exact prefixLift 3452127
  have htrace : WordTrace (prefixWord ++ tailWord_3452127) baseStart_3452127 baseEnd_3452127 := by
    simpa [prefixWord, tailWord_3452127, baseEnd_3452127] using wordTrace_append hprefix tailTrace_3452127
  have hstable : (prefixWord ++ tailWord_3452127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452127).length < 2 ^ (prefixWord ++ tailWord_3452127).sum := by decide
  have hdescent : baseEnd_3452127 < baseStart_3452127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452147 : List Nat := [1, 1, 1, 2, 2, 7, 1, 2, 1, 5]
def baseStart_3452147 : Nat := 118140960795 + 3452147 * 2 ^ 59
def prefixEnd_3452147 : Nat := 4983230072969 + 3 ^ 40 * 3452147 * 2
def baseEnd_3452147 : Nat := 590870233658936730895457

theorem tailTrace_3452147 : CollatzResearch.WordTrace tailWord_3452147 prefixEnd_3452147 590870233658936730895457 := by
  unfold tailWord_3452147
  simp only [CollatzResearch.WordTrace]
  refine ⟨125910145024468473613866695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83940096682978982409244463 125910145024468473613866695)
  ·
    refine ⟨188865217536702710420800043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125910145024468473613866695 188865217536702710420800043)
    ·
      refine ⟨283297826305054065631200065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188865217536702710420800043 283297826305054065631200065)
      ·
        refine ⟨212473369728790549223400049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283297826305054065631200065 212473369728790549223400049)
        ·
          refine ⟨159355027296592911917550037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212473369728790549223400049 159355027296592911917550037)
          ·
            refine ⟨3734883452263896373067579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 159355027296592911917550037 3734883452263896373067579)
            ·
              refine ⟨5602325178395844559601369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3734883452263896373067579 5602325178395844559601369)
              ·
                refine ⟨4201743883796883419701027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5602325178395844559601369 4201743883796883419701027)
                ·
                  refine ⟨6302615825695325129551541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4201743883796883419701027 6302615825695325129551541)
                  ·
                    refine ⟨590870233658936730895457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6302615825695325129551541 590870233658936730895457)
                    ·
                      rfl

theorem cell23_3452147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 2, 1, 5].length) (baseStart_3452147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452147 prefixEnd_3452147 := by exact prefixLift 3452147
  have htrace : WordTrace (prefixWord ++ tailWord_3452147) baseStart_3452147 baseEnd_3452147 := by
    simpa [prefixWord, tailWord_3452147, baseEnd_3452147] using wordTrace_append hprefix tailTrace_3452147
  have hstable : (prefixWord ++ tailWord_3452147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452147).length < 2 ^ (prefixWord ++ tailWord_3452147).sum := by decide
  have hdescent : baseEnd_3452147 < baseStart_3452147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452148 : List Nat := [2, 6, 1, 2, 1, 1, 2, 1, 2, 2, 3]
def baseStart_3452148 : Nat := 118140960795 + 3452148 * 2 ^ 59
def prefixEnd_3452148 : Nat := 4983230072969 + 3 ^ 40 * 3452148 * 2
def baseEnd_3452148 : Nat := 1772611214457464688773867

theorem tailTrace_3452148 : CollatzResearch.WordTrace tailWord_3452148 prefixEnd_3452148 1772611214457464688773867 := by
  unfold tailWord_3452148
  simp only [CollatzResearch.WordTrace]
  refine ⟨62955090748732425392326549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83940120998309900523102065 62955090748732425392326549)
  ·
    refine ⟨2951019878846832440265307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 62955090748732425392326549 2951019878846832440265307)
    ·
      refine ⟨4426529818270248660397961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2951019878846832440265307 4426529818270248660397961)
      ·
        refine ⟨3319897363702686495298471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4426529818270248660397961 3319897363702686495298471)
        ·
          refine ⟨4979846045554029742947707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3319897363702686495298471 4979846045554029742947707)
          ·
            refine ⟨7469769068331044614421561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4979846045554029742947707 7469769068331044614421561)
            ·
              refine ⟨5602326801248283460816171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7469769068331044614421561 5602326801248283460816171)
              ·
                refine ⟨8403490201872425191224257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5602326801248283460816171 8403490201872425191224257)
                ·
                  refine ⟨6302617651404318893418193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8403490201872425191224257 6302617651404318893418193)
                  ·
                    refine ⟨4726963238553239170063645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6302617651404318893418193 4726963238553239170063645)
                    ·
                      refine ⟨1772611214457464688773867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4726963238553239170063645 1772611214457464688773867)
                      ·
                        rfl

theorem cell23_3452148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_3452148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452148 prefixEnd_3452148 := by exact prefixLift 3452148
  have htrace : WordTrace (prefixWord ++ tailWord_3452148) baseStart_3452148 baseEnd_3452148 := by
    simpa [prefixWord, tailWord_3452148, baseEnd_3452148] using wordTrace_append hprefix tailTrace_3452148
  have hstable : (prefixWord ++ tailWord_3452148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452148).length < 2 ^ (prefixWord ++ tailWord_3452148).sum := by decide
  have hdescent : baseEnd_3452148 < baseStart_3452148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452164 : List Nat := [2, 3, 2, 2, 2, 2, 3, 1, 1, 5]
def baseStart_3452164 : Nat := 118140960795 + 3452164 * 2 ^ 59
def prefixEnd_3452164 : Nat := 4983230072969 + 3 ^ 40 * 3452164 * 2
def baseEnd_3452164 : Nat := 590873143382645542057931

theorem tailTrace_3452164 : CollatzResearch.WordTrace tailWord_3452164 prefixEnd_3452164 590873143382645542057931 := by
  unfold tailWord_3452164
  simp only [CollatzResearch.WordTrace]
  refine ⟨62955382532703442758617773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83940510043604590344823697 62955382532703442758617773)
  ·
    refine ⟨23608268449763791034481665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62955382532703442758617773 23608268449763791034481665)
    ·
      refine ⟨17706201337322843275861249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23608268449763791034481665 17706201337322843275861249)
      ·
        refine ⟨13279651002992132456895937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17706201337322843275861249 13279651002992132456895937)
        ·
          refine ⟨9959738252244099342671953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13279651002992132456895937 9959738252244099342671953)
          ·
            refine ⟨7469803689183074507003965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9959738252244099342671953 7469803689183074507003965)
            ·
              refine ⟨2801176383443652940126487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7469803689183074507003965 2801176383443652940126487)
              ·
                refine ⟨4201764575165479410189731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2801176383443652940126487 4201764575165479410189731)
                ·
                  refine ⟨6302646862748219115284597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4201764575165479410189731 6302646862748219115284597)
                  ·
                    refine ⟨590873143382645542057931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6302646862748219115284597 590873143382645542057931)
                    ·
                      rfl

theorem cell23_3452164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_3452164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452164 prefixEnd_3452164 := by exact prefixLift 3452164
  have htrace : WordTrace (prefixWord ++ tailWord_3452164) baseStart_3452164 baseEnd_3452164 := by
    simpa [prefixWord, tailWord_3452164, baseEnd_3452164] using wordTrace_append hprefix tailTrace_3452164
  have hstable : (prefixWord ++ tailWord_3452164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452164).length < 2 ^ (prefixWord ++ tailWord_3452164).sum := by decide
  have hdescent : baseEnd_3452164 < baseStart_3452164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452177 : List Nat := [1, 2, 2, 1, 1, 4, 4, 2, 2, 4]
def baseStart_3452177 : Nat := 118140960795 + 3452177 * 2 ^ 59
def prefixEnd_3452177 : Nat := 4983230072969 + 3 ^ 40 * 3452177 * 2
def baseEnd_3452177 : Nat := 590875368465481691770411

theorem tailTrace_3452177 : CollatzResearch.WordTrace tailWord_3452177 prefixEnd_3452177 590875368465481691770411 := by
  unfold tailWord_3452177
  simp only [CollatzResearch.WordTrace]
  refine ⟨125911239214359788737458785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83940826142906525824972523 125911239214359788737458785)
  ·
    refine ⟨94433429410769841553094089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125911239214359788737458785 94433429410769841553094089)
    ·
      refine ⟨70825072058077381164820567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94433429410769841553094089 70825072058077381164820567)
      ·
        refine ⟨106237608087116071747230851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70825072058077381164820567 106237608087116071747230851)
        ·
          refine ⟨159356412130674107620846277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106237608087116071747230851 159356412130674107620846277)
          ·
            refine ⟨29879327274501395178908677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159356412130674107620846277 29879327274501395178908677)
            ·
              refine ⟨5602373863969011596045377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29879327274501395178908677 5602373863969011596045377)
              ·
                refine ⟨4201780397976758697034033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5602373863969011596045377 4201780397976758697034033)
                ·
                  refine ⟨3151335298482569022775525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4201780397976758697034033 3151335298482569022775525)
                  ·
                    refine ⟨590875368465481691770411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3151335298482569022775525 590875368465481691770411)
                    ·
                      rfl

theorem cell23_3452177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 2, 2, 4].length) (baseStart_3452177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452177 prefixEnd_3452177 := by exact prefixLift 3452177
  have htrace : WordTrace (prefixWord ++ tailWord_3452177) baseStart_3452177 baseEnd_3452177 := by
    simpa [prefixWord, tailWord_3452177, baseEnd_3452177] using wordTrace_append hprefix tailTrace_3452177
  have hstable : (prefixWord ++ tailWord_3452177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452177).length < 2 ^ (prefixWord ++ tailWord_3452177).sum := by decide
  have hdescent : baseEnd_3452177 < baseStart_3452177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452197 : List Nat := [1, 3, 1, 2, 4, 2, 2, 1, 1, 2, 4]
def baseStart_3452197 : Nat := 118140960795 + 3452197 * 2 ^ 59
def prefixEnd_3452197 : Nat := 4983230072969 + 3 ^ 40 * 3452197 * 2
def baseEnd_3452197 : Nat := 1772636375009534997061141

theorem tailTrace_3452197 : CollatzResearch.WordTrace tailWord_3452197 prefixEnd_3452197 1772636375009534997061141 := by
  unfold tailWord_3452197
  simp only [CollatzResearch.WordTrace]
  refine ⟨125911968674287332153186845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83941312449524888102124563 125911968674287332153186845)
  ·
    refine ⟨47216988252857749557445067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125911968674287332153186845 47216988252857749557445067)
    ·
      refine ⟨70825482379286624336167601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47216988252857749557445067 70825482379286624336167601)
      ·
        refine ⟨53119111784464968252125701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70825482379286624336167601 53119111784464968252125701)
        ·
          refine ⟨9959833459587181547273569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53119111784464968252125701 9959833459587181547273569)
          ·
            refine ⟨7469875094690386160455177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9959833459587181547273569 7469875094690386160455177)
            ·
              refine ⟨5602406321017789620341383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7469875094690386160455177 5602406321017789620341383)
              ·
                refine ⟨8403609481526684430512075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5602406321017789620341383 8403609481526684430512075)
                ·
                  refine ⟨12605414222290026645768113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8403609481526684430512075 12605414222290026645768113)
                  ·
                    refine ⟨9454060666717519984326085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12605414222290026645768113 9454060666717519984326085)
                    ·
                      refine ⟨1772636375009534997061141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9454060666717519984326085 1772636375009534997061141)
                      ·
                        rfl

theorem cell23_3452197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 2, 4].length) (baseStart_3452197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452197 prefixEnd_3452197 := by exact prefixLift 3452197
  have htrace : WordTrace (prefixWord ++ tailWord_3452197) baseStart_3452197 baseEnd_3452197 := by
    simpa [prefixWord, tailWord_3452197, baseEnd_3452197] using wordTrace_append hprefix tailTrace_3452197
  have hstable : (prefixWord ++ tailWord_3452197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452197).length < 2 ^ (prefixWord ++ tailWord_3452197).sum := by decide
  have hdescent : baseEnd_3452197 < baseStart_3452197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452221 : List Nat := [1, 4, 1, 5, 1, 1, 1, 3, 1, 2, 3]
def baseStart_3452221 : Nat := 118140960795 + 3452221 * 2 ^ 59
def prefixEnd_3452221 : Nat := 4983230072969 + 3 ^ 40 * 3452221 * 2
def baseEnd_3452221 : Nat := 1772648698545242903161031

theorem tailTrace_3452221 : CollatzResearch.WordTrace tailWord_3452221 prefixEnd_3452221 1772648698545242903161031 := by
  unfold tailWord_3452221
  simp only [CollatzResearch.WordTrace]
  refine ⟨125912844026200384252060517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83941896017466922834707011 125912844026200384252060517)
  ·
    refine ⟨23608658254912572047261347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125912844026200384252060517 23608658254912572047261347)
    ·
      refine ⟨35412987382368858070892021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23608658254912572047261347 35412987382368858070892021)
      ·
        refine ⟨3319967567097080444146127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35412987382368858070892021 3319967567097080444146127)
        ·
          refine ⟨4979951350645620666219191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3319967567097080444146127 4979951350645620666219191)
          ·
            refine ⟨7469927025968430999328787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4979951350645620666219191 7469927025968430999328787)
            ·
              refine ⟨11204890538952646498993181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7469927025968430999328787 11204890538952646498993181)
              ·
                refine ⟨4201833952107242437122443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11204890538952646498993181 4201833952107242437122443)
                ·
                  refine ⟨6302750928160863655683665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4201833952107242437122443 6302750928160863655683665)
                  ·
                    refine ⟨4727063196120647741762749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6302750928160863655683665 4727063196120647741762749)
                    ·
                      refine ⟨1772648698545242903161031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4727063196120647741762749 1772648698545242903161031)
                      ·
                        rfl

theorem cell23_3452221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_3452221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452221 prefixEnd_3452221 := by exact prefixLift 3452221
  have htrace : WordTrace (prefixWord ++ tailWord_3452221) baseStart_3452221 baseEnd_3452221 := by
    simpa [prefixWord, tailWord_3452221, baseEnd_3452221] using wordTrace_append hprefix tailTrace_3452221
  have hstable : (prefixWord ++ tailWord_3452221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452221).length < 2 ^ (prefixWord ++ tailWord_3452221).sum := by decide
  have hdescent : baseEnd_3452221 < baseStart_3452221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452250 : List Nat := [3, 1, 1, 2, 1, 2, 4, 1, 2, 6]
def baseStart_3452250 : Nat := 118140960795 + 3452250 * 2 ^ 59
def prefixEnd_3452250 : Nat := 4983230072969 + 3 ^ 40 * 3452250 * 2
def baseEnd_3452250 : Nat := 590887863161407763232799

theorem tailTrace_3452250 : CollatzResearch.WordTrace tailWord_3452250 prefixEnd_3452250 590887863161407763232799 := by
  unfold tailWord_3452250
  simp only [CollatzResearch.WordTrace]
  refine ⟨31478475435773830551216551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83942601162063548136577469 31478475435773830551216551)
  ·
    refine ⟨47217713153660745826824827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31478475435773830551216551 47217713153660745826824827)
    ·
      refine ⟨70826569730491118740237241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47217713153660745826824827 70826569730491118740237241)
      ·
        refine ⟨53119927297868339055177931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70826569730491118740237241 53119927297868339055177931)
        ·
          refine ⟨79679890946802508582766897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53119927297868339055177931 79679890946802508582766897)
          ·
            refine ⟨59759918210101881437075173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79679890946802508582766897 59759918210101881437075173)
            ·
              refine ⟨11204984664394102769451595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59759918210101881437075173 11204984664394102769451595)
              ·
                refine ⟨16807476996591154154177393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11204984664394102769451595 16807476996591154154177393)
                ·
                  refine ⟨12605607747443365615633045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16807476996591154154177393 12605607747443365615633045)
                  ·
                    refine ⟨590887863161407763232799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12605607747443365615633045 590887863161407763232799)
                    ·
                      rfl

theorem cell23_3452250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 2, 6].length) (baseStart_3452250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452250 prefixEnd_3452250 := by exact prefixLift 3452250
  have htrace : WordTrace (prefixWord ++ tailWord_3452250) baseStart_3452250 baseEnd_3452250 := by
    simpa [prefixWord, tailWord_3452250, baseEnd_3452250] using wordTrace_append hprefix tailTrace_3452250
  have hstable : (prefixWord ++ tailWord_3452250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452250).length < 2 ^ (prefixWord ++ tailWord_3452250).sum := by decide
  have hdescent : baseEnd_3452250 < baseStart_3452250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452274 : List Nat := [3, 2, 1, 2, 1, 2, 1, 1, 6, 2, 2]
def baseStart_3452274 : Nat := 118140960795 + 3452274 * 2 ^ 59
def prefixEnd_3452274 : Nat := 4983230072969 + 3 ^ 40 * 3452274 * 2
def baseEnd_3452274 : Nat := 1772675913019931195798287

theorem tailTrace_3452274 : CollatzResearch.WordTrace tailWord_3452274 prefixEnd_3452274 1772675913019931195798287 := by
  unfold tailWord_3452274
  simp only [CollatzResearch.WordTrace]
  refine ⟨31478694273752093575934969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83943184730005582869159917 31478694273752093575934969)
  ·
    refine ⟨23609020705314070181951227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31478694273752093575934969 23609020705314070181951227)
    ·
      refine ⟨35413531057971105272926841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23609020705314070181951227 35413531057971105272926841)
      ·
        refine ⟨26560148293478328954695131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35413531057971105272926841 26560148293478328954695131)
        ·
          refine ⟨39840222440217493432042697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26560148293478328954695131 39840222440217493432042697)
          ·
            refine ⟨29880166830163120074032023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39840222440217493432042697 29880166830163120074032023)
            ·
              refine ⟨44820250245244680111048035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29880166830163120074032023 44820250245244680111048035)
              ·
                refine ⟨67230375367867020166572053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44820250245244680111048035 67230375367867020166572053)
                ·
                  refine ⟨3151423845368766570308065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 67230375367867020166572053 3151423845368766570308065)
                  ·
                    refine ⟨2363567884026574927731049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3151423845368766570308065 2363567884026574927731049)
                    ·
                      refine ⟨1772675913019931195798287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2363567884026574927731049 1772675913019931195798287)
                      ·
                        rfl

theorem cell23_3452274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 6, 2, 2].length) (baseStart_3452274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452274 prefixEnd_3452274 := by exact prefixLift 3452274
  have htrace : WordTrace (prefixWord ++ tailWord_3452274) baseStart_3452274 baseEnd_3452274 := by
    simpa [prefixWord, tailWord_3452274, baseEnd_3452274] using wordTrace_append hprefix tailTrace_3452274
  have hstable : (prefixWord ++ tailWord_3452274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452274).length < 2 ^ (prefixWord ++ tailWord_3452274).sum := by decide
  have hdescent : baseEnd_3452274 < baseStart_3452274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452308 : List Nat := [2, 4, 2, 1, 2, 2, 1, 3, 2, 2, 2]
def baseStart_3452308 : Nat := 118140960795 + 3452308 * 2 ^ 59
def prefixEnd_3452308 : Nat := 4983230072969 + 3 ^ 40 * 3452308 * 2
def baseEnd_3452308 : Nat := 1772693371362184062773131

theorem tailTrace_3452308 : CollatzResearch.WordTrace tailWord_3452308 prefixEnd_3452308 1772693371362184062773131 := by
  unfold tailWord_3452308
  simp only [CollatzResearch.WordTrace]
  refine ⟨62958008588442599055238789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83944011451256798740318385 62958008588442599055238789)
  ·
    refine ⟨11804626610332987322857273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62958008588442599055238789 11804626610332987322857273)
    ·
      refine ⟨8853469957749740492142955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11804626610332987322857273 8853469957749740492142955)
      ·
        refine ⟨13280204936624610738214433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8853469957749740492142955 13280204936624610738214433)
        ·
          refine ⟨9960153702468458053660825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13280204936624610738214433 9960153702468458053660825)
          ·
            refine ⟨7470115276851343540245619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9960153702468458053660825 7470115276851343540245619)
            ·
              refine ⟨11205172915277015310368429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7470115276851343540245619 11205172915277015310368429)
              ·
                refine ⟨4201939843228880741388161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11205172915277015310368429 4201939843228880741388161)
                ·
                  refine ⟨3151454882421660556041121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4201939843228880741388161 3151454882421660556041121)
                  ·
                    refine ⟨2363591161816245417030841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3151454882421660556041121 2363591161816245417030841)
                    ·
                      refine ⟨1772693371362184062773131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2363591161816245417030841 1772693371362184062773131)
                      ·
                        rfl

theorem cell23_3452308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_3452308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452308 prefixEnd_3452308 := by exact prefixLift 3452308
  have htrace : WordTrace (prefixWord ++ tailWord_3452308) baseStart_3452308 baseEnd_3452308 := by
    simpa [prefixWord, tailWord_3452308, baseEnd_3452308] using wordTrace_append hprefix tailTrace_3452308
  have hstable : (prefixWord ++ tailWord_3452308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452308).length < 2 ^ (prefixWord ++ tailWord_3452308).sum := by decide
  have hdescent : baseEnd_3452308 < baseStart_3452308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452320 : List Nat := [2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 7]
def baseStart_3452320 : Nat := 118140960795 + 3452320 * 2 ^ 59
def prefixEnd_3452320 : Nat := 4983230072969 + 3 ^ 40 * 3452320 * 2
def baseEnd_3452320 : Nat := 1772699533130038015823075

theorem tailTrace_3452320 : CollatzResearch.WordTrace tailWord_3452320 prefixEnd_3452320 1772699533130038015823075 := by
  unfold tailWord_3452320
  simp only [CollatzResearch.WordTrace]
  refine ⟨62958227426420862079957207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83944303235227816106609609 62958227426420862079957207)
  ·
    refine ⟨94437341139631293119935811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62958227426420862079957207 94437341139631293119935811)
    ·
      refine ⟨141656011709446939679903717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94437341139631293119935811 141656011709446939679903717)
      ·
        refine ⟨26560502195521301189981947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141656011709446939679903717 26560502195521301189981947)
        ·
          refine ⟨39840753293281951784972921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26560502195521301189981947 39840753293281951784972921)
          ·
            refine ⟨29880564969961463838729691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39840753293281951784972921 29880564969961463838729691)
            ·
              refine ⟨44820847454942195758094537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29880564969961463838729691 44820847454942195758094537)
              ·
                refine ⟨33615635591206646818570903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44820847454942195758094537 33615635591206646818570903)
                ·
                  refine ⟨50423453386809970227856355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33615635591206646818570903 50423453386809970227856355)
                  ·
                    refine ⟨75635180080214955341784533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50423453386809970227856355 75635180080214955341784533)
                    ·
                      refine ⟨1772699533130038015823075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 75635180080214955341784533 1772699533130038015823075)
                      ·
                        rfl

theorem cell23_3452320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_3452320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452320 prefixEnd_3452320 := by exact prefixLift 3452320
  have htrace : WordTrace (prefixWord ++ tailWord_3452320) baseStart_3452320 baseEnd_3452320 := by
    simpa [prefixWord, tailWord_3452320, baseEnd_3452320] using wordTrace_append hprefix tailTrace_3452320
  have hstable : (prefixWord ++ tailWord_3452320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452320).length < 2 ^ (prefixWord ++ tailWord_3452320).sum := by decide
  have hdescent : baseEnd_3452320 < baseStart_3452320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452348 : List Nat := [2, 2, 2, 4, 2, 2, 2, 2, 5]
def baseStart_3452348 : Nat := 118140960795 + 3452348 * 2 ^ 59
def prefixEnd_3452348 : Nat := 4983230072969 + 3 ^ 40 * 3452348 * 2
def baseEnd_3452348 : Nat := 196968212287595989585883

theorem tailTrace_3452348 : CollatzResearch.WordTrace tailWord_3452348 prefixEnd_3452348 196968212287595989585883 := by
  unfold tailWord_3452348
  simp only [CollatzResearch.WordTrace]
  refine ⟨62958738048370142470966849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83944984064493523294622465 62958738048370142470966849)
  ·
    refine ⟨47219053536277606853225137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62958738048370142470966849 47219053536277606853225137)
    ·
      refine ⟨35414290152208205139918853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47219053536277606853225137 35414290152208205139918853)
      ·
        refine ⟨6640179403539038463734785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35414290152208205139918853 6640179403539038463734785)
        ·
          refine ⟨4980134552654278847801089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6640179403539038463734785 4980134552654278847801089)
          ·
            refine ⟨3735100914490709135850817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4980134552654278847801089 3735100914490709135850817)
            ·
              refine ⟨2801325685868031851888113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3735100914490709135850817 2801325685868031851888113)
              ·
                refine ⟨2100994264401023888916085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2801325685868031851888113 2100994264401023888916085)
                ·
                  refine ⟨196968212287595989585883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2100994264401023888916085 196968212287595989585883)
                  ·
                    rfl

theorem cell23_3452348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 2, 5].length) (baseStart_3452348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452348 prefixEnd_3452348 := by exact prefixLift 3452348
  have htrace : WordTrace (prefixWord ++ tailWord_3452348) baseStart_3452348 baseEnd_3452348 := by
    simpa [prefixWord, tailWord_3452348, baseEnd_3452348] using wordTrace_append hprefix tailTrace_3452348
  have hstable : (prefixWord ++ tailWord_3452348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452348).length < 2 ^ (prefixWord ++ tailWord_3452348).sum := by decide
  have hdescent : baseEnd_3452348 < baseStart_3452348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452364 : List Nat := [2, 2, 1, 4, 2, 1, 1, 1, 1, 6, 2]
def baseStart_3452364 : Nat := 118140960795 + 3452364 * 2 ^ 59
def prefixEnd_3452364 : Nat := 4983230072969 + 3 ^ 40 * 3452364 * 2
def baseEnd_3452364 : Nat := 1772722126278835843672873

theorem tailTrace_3452364 : CollatzResearch.WordTrace tailWord_3452364 prefixEnd_3452364 1772722126278835843672873 := by
  unfold tailWord_3452364
  simp only [CollatzResearch.WordTrace]
  refine ⟨62959029832341159837258073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83945373109788213116344097 62959029832341159837258073)
  ·
    refine ⟨47219272374255869877943555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62959029832341159837258073 47219272374255869877943555)
    ·
      refine ⟨70828908561383804816915333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47219272374255869877943555 70828908561383804816915333)
      ·
        refine ⟨13280420355259463403171625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70828908561383804816915333 13280420355259463403171625)
        ·
          refine ⟨9960315266444597552378719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13280420355259463403171625 9960315266444597552378719)
          ·
            refine ⟨14940472899666896328568079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9960315266444597552378719 14940472899666896328568079)
            ·
              refine ⟨22410709349500344492852119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14940472899666896328568079 22410709349500344492852119)
              ·
                refine ⟨33616064024250516739278179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22410709349500344492852119 33616064024250516739278179)
                ·
                  refine ⟨50424096036375775108917269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33616064024250516739278179 50424096036375775108917269)
                  ·
                    refine ⟨2363629501705114458230497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 50424096036375775108917269 2363629501705114458230497)
                    ·
                      refine ⟨1772722126278835843672873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2363629501705114458230497 1772722126278835843672873)
                      ·
                        rfl

theorem cell23_3452364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_3452364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452364 prefixEnd_3452364 := by exact prefixLift 3452364
  have htrace : WordTrace (prefixWord ++ tailWord_3452364) baseStart_3452364 baseEnd_3452364 := by
    simpa [prefixWord, tailWord_3452364, baseEnd_3452364] using wordTrace_append hprefix tailTrace_3452364
  have hstable : (prefixWord ++ tailWord_3452364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452364).length < 2 ^ (prefixWord ++ tailWord_3452364).sum := by decide
  have hdescent : baseEnd_3452364 < baseStart_3452364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452367 : List Nat := [1, 1, 2, 1, 1, 4, 2, 2, 4, 2, 3]
def baseStart_3452367 : Nat := 118140960795 + 3452367 * 2 ^ 59
def prefixEnd_3452367 : Nat := 4983230072969 + 3 ^ 40 * 3452367 * 2
def baseEnd_3452367 : Nat := 1772723666720799331935359

theorem tailTrace_3452367 : CollatzResearch.WordTrace tailWord_3452367 prefixEnd_3452367 1772723666720799331935359 := by
  unfold tailWord_3452367
  simp only [CollatzResearch.WordTrace]
  refine ⟨125918169083671451186875355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83945446055780967457916903 125918169083671451186875355)
  ·
    refine ⟨188877253625507176780313033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125918169083671451186875355 188877253625507176780313033)
    ·
      refine ⟨141657940219130382585234775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188877253625507176780313033 141657940219130382585234775)
      ·
        refine ⟨212486910328695573877852163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141657940219130382585234775 212486910328695573877852163)
        ·
          refine ⟨318730365493043360816778245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212486910328695573877852163 318730365493043360816778245)
          ·
            refine ⟨59761943529945630153145921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 318730365493043360816778245 59761943529945630153145921)
            ·
              refine ⟨44821457647459222614859441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59761943529945630153145921 44821457647459222614859441)
              ·
                refine ⟨33616093235594416961144581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44821457647459222614859441 33616093235594416961144581)
                ·
                  refine ⟨6303017481673953180214609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33616093235594416961144581 6303017481673953180214609)
                  ·
                    refine ⟨4727263111255464885160957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6303017481673953180214609 4727263111255464885160957)
                    ·
                      refine ⟨1772723666720799331935359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4727263111255464885160957 1772723666720799331935359)
                      ·
                        rfl

theorem cell23_3452367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 4, 2, 3].length) (baseStart_3452367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452367 prefixEnd_3452367 := by exact prefixLift 3452367
  have htrace : WordTrace (prefixWord ++ tailWord_3452367) baseStart_3452367 baseEnd_3452367 := by
    simpa [prefixWord, tailWord_3452367, baseEnd_3452367] using wordTrace_append hprefix tailTrace_3452367
  have hstable : (prefixWord ++ tailWord_3452367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452367).length < 2 ^ (prefixWord ++ tailWord_3452367).sum := by decide
  have hdescent : baseEnd_3452367 < baseStart_3452367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452381 : List Nat := [1, 4, 3, 1, 1, 4, 1, 1, 2, 1, 4]
def baseStart_3452381 : Nat := 118140960795 + 3452381 * 2 ^ 59
def prefixEnd_3452381 : Nat := 4983230072969 + 3 ^ 40 * 3452381 * 2
def baseEnd_3452381 : Nat := 1772730855449962277160295

theorem tailTrace_3452381 : CollatzResearch.WordTrace tailWord_3452381 prefixEnd_3452381 1772730855449962277160295 := by
  unfold tailWord_3452381
  simp only [CollatzResearch.WordTrace]
  refine ⟨125918679705620731577884997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83945786470413821051923331 125918679705620731577884997)
  ·
    refine ⟨23609752444803887170853437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125918679705620731577884997 23609752444803887170853437)
    ·
      refine ⟨8853657166801457689070039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23609752444803887170853437 8853657166801457689070039)
      ·
        refine ⟨13280485750202186533605059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8853657166801457689070039 13280485750202186533605059)
        ·
          refine ⟨19920728625303279800407589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13280485750202186533605059 19920728625303279800407589)
          ·
            refine ⟨3735136617244364962576423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19920728625303279800407589 3735136617244364962576423)
            ·
              refine ⟨5602704925866547443864635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3735136617244364962576423 5602704925866547443864635)
              ·
                refine ⟨8404057388799821165796953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5602704925866547443864635 8404057388799821165796953)
                ·
                  refine ⟨6303043041599865874347715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8404057388799821165796953 6303043041599865874347715)
                  ·
                    refine ⟨9454564562399798811521573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6303043041599865874347715 9454564562399798811521573)
                    ·
                      refine ⟨1772730855449962277160295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9454564562399798811521573 1772730855449962277160295)
                      ·
                        rfl

theorem cell23_3452381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_3452381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452381 prefixEnd_3452381 := by exact prefixLift 3452381
  have htrace : WordTrace (prefixWord ++ tailWord_3452381) baseStart_3452381 baseEnd_3452381 := by
    simpa [prefixWord, tailWord_3452381, baseEnd_3452381] using wordTrace_append hprefix tailTrace_3452381
  have hstable : (prefixWord ++ tailWord_3452381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452381).length < 2 ^ (prefixWord ++ tailWord_3452381).sum := by decide
  have hdescent : baseEnd_3452381 < baseStart_3452381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452391 : List Nat := [1, 1, 5, 2, 1, 2, 1, 5, 1, 4]
def baseStart_3452391 : Nat := 118140960795 + 3452391 * 2 ^ 59
def prefixEnd_3452391 : Nat := 4983230072969 + 3 ^ 40 * 3452391 * 2
def baseEnd_3452391 : Nat := 590911996752169079345083

theorem tailTrace_3452391 : CollatzResearch.WordTrace tailWord_3452391 prefixEnd_3452391 590911996752169079345083 := by
  unfold tailWord_3452391
  simp only [CollatzResearch.WordTrace]
  refine ⟨125919044435584503285749027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83946029623723002190499351 125919044435584503285749027)
  ·
    refine ⟨188878566653376754928623541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125919044435584503285749027 188878566653376754928623541)
    ·
      refine ⟨17707365623754070774558457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 188878566653376754928623541 17707365623754070774558457)
      ·
        refine ⟨13280524217815553080918843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17707365623754070774558457 13280524217815553080918843)
        ·
          refine ⟨19920786326723329621378265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13280524217815553080918843 19920786326723329621378265)
          ·
            refine ⟨14940589745042497216033699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19920786326723329621378265 14940589745042497216033699)
            ·
              refine ⟨22410884617563745824050549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14940589745042497216033699 22410884617563745824050549)
              ·
                refine ⟨2101020432896601171004739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22410884617563745824050549 2101020432896601171004739)
                ·
                  refine ⟨3151530649344901756507109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2101020432896601171004739 3151530649344901756507109)
                  ·
                    refine ⟨590911996752169079345083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3151530649344901756507109 590911996752169079345083)
                    ·
                      rfl

theorem cell23_3452391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_3452391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452391 prefixEnd_3452391 := by exact prefixLift 3452391
  have htrace : WordTrace (prefixWord ++ tailWord_3452391) baseStart_3452391 baseEnd_3452391 := by
    simpa [prefixWord, tailWord_3452391, baseEnd_3452391] using wordTrace_append hprefix tailTrace_3452391
  have hstable : (prefixWord ++ tailWord_3452391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452391).length < 2 ^ (prefixWord ++ tailWord_3452391).sum := by decide
  have hdescent : baseEnd_3452391 < baseStart_3452391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452424 : List Nat := [2, 1, 3, 2, 1, 1, 3, 2, 1, 5, 2]
def baseStart_3452424 : Nat := 118140960795 + 3452424 * 2 ^ 59
def prefixEnd_3452424 : Nat := 4983230072969 + 3 ^ 40 * 3452424 * 2
def baseEnd_3452424 : Nat := 1772752935118105608922597

theorem tailTrace_3452424 : CollatzResearch.WordTrace tailWord_3452424 prefixEnd_3452424 1772752935118105608922597 := by
  unfold tailWord_3452424
  simp only [CollatzResearch.WordTrace]
  refine ⟨62960124022232474960850163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83946832029643299947800217 62960124022232474960850163)
  ·
    refine ⟨94440186033348712441275245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62960124022232474960850163 94440186033348712441275245)
    ·
      refine ⟨35415069762505767165478217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94440186033348712441275245 35415069762505767165478217)
      ·
        refine ⟨26561302321879325374108663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35415069762505767165478217 26561302321879325374108663)
        ·
          refine ⟨39841953482818988061162995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26561302321879325374108663 39841953482818988061162995)
          ·
            refine ⟨59762930224228482091744493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39841953482818988061162995 59762930224228482091744493)
            ·
              refine ⟨22411098834085680784404185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59762930224228482091744493 22411098834085680784404185)
              ·
                refine ⟨16808324125564260588303139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22411098834085680784404185 16808324125564260588303139)
                ·
                  refine ⟨25212486188346390882454709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16808324125564260588303139 25212486188346390882454709)
                  ·
                    refine ⟨2363670580157474145230129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25212486188346390882454709 2363670580157474145230129)
                    ·
                      refine ⟨1772752935118105608922597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2363670580157474145230129 1772752935118105608922597)
                      ·
                        rfl

theorem cell23_3452424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 1, 5, 2].length) (baseStart_3452424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452424 prefixEnd_3452424 := by exact prefixLift 3452424
  have htrace : WordTrace (prefixWord ++ tailWord_3452424) baseStart_3452424 baseEnd_3452424 := by
    simpa [prefixWord, tailWord_3452424, baseEnd_3452424] using wordTrace_append hprefix tailTrace_3452424
  have hstable : (prefixWord ++ tailWord_3452424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452424).length < 2 ^ (prefixWord ++ tailWord_3452424).sum := by decide
  have hdescent : baseEnd_3452424 < baseStart_3452424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452447 : List Nat := [1, 1, 2, 4, 1, 1, 2, 4, 1, 6]
def baseStart_3452447 : Nat := 118140960795 + 3452447 * 2 ^ 59
def prefixEnd_3452447 : Nat := 4983230072969 + 3 ^ 40 * 3452447 * 2
def baseEnd_3452447 : Nat := 590921581724386339644997

theorem tailTrace_3452447 : CollatzResearch.WordTrace tailWord_3452447 prefixEnd_3452447 590921581724386339644997 := by
  unfold tailWord_3452447
  simp only [CollatzResearch.WordTrace]
  refine ⟨125921086923381624849787595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83947391282254416566525063 125921086923381624849787595)
  ·
    refine ⟨188881630385072437274681393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125921086923381624849787595 188881630385072437274681393)
    ·
      refine ⟨141661222788804327956011045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188881630385072437274681393 141661222788804327956011045)
      ·
        refine ⟨26561479272900811491752071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141661222788804327956011045 26561479272900811491752071)
        ·
          refine ⟨39842218909351217237628107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26561479272900811491752071 39842218909351217237628107)
          ·
            refine ⟨59763328364026825856442161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39842218909351217237628107 59763328364026825856442161)
            ·
              refine ⟨44822496273020119392331621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59763328364026825856442161 44822496273020119392331621)
              ·
                refine ⟨8404218051191272386062179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44822496273020119392331621 8404218051191272386062179)
                ·
                  refine ⟨12606327076786908579093269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8404218051191272386062179 12606327076786908579093269)
                  ·
                    refine ⟨590921581724386339644997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12606327076786908579093269 590921581724386339644997)
                    ·
                      rfl

theorem cell23_3452447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 6].length) (baseStart_3452447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452447 prefixEnd_3452447 := by exact prefixLift 3452447
  have htrace : WordTrace (prefixWord ++ tailWord_3452447) baseStart_3452447 baseEnd_3452447 := by
    simpa [prefixWord, tailWord_3452447, baseEnd_3452447] using wordTrace_append hprefix tailTrace_3452447
  have hstable : (prefixWord ++ tailWord_3452447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452447).length < 2 ^ (prefixWord ++ tailWord_3452447).sum := by decide
  have hdescent : baseEnd_3452447 < baseStart_3452447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452464 : List Nat := [2, 1, 1, 1, 2, 3, 1, 6, 2, 4]
def baseStart_3452464 : Nat := 118140960795 + 3452464 * 2 ^ 59
def prefixEnd_3452464 : Nat := 4983230072969 + 3 ^ 40 * 3452464 * 2
def baseEnd_3452464 : Nat := 590924491448095150807471

theorem tailTrace_3452464 : CollatzResearch.WordTrace tailWord_3452464 prefixEnd_3452464 590924491448095150807471 := by
  unfold tailWord_3452464
  simp only [CollatzResearch.WordTrace]
  refine ⟨62960853482160018376578223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83947804642880024502104297 62960853482160018376578223)
  ·
    refine ⟨94441280223240027564867335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62960853482160018376578223 94441280223240027564867335)
    ·
      refine ⟨141661920334860041347301003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94441280223240027564867335 141661920334860041347301003)
      ·
        refine ⟨212492880502290062020951505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141661920334860041347301003 212492880502290062020951505)
        ·
          refine ⟨159369660376717546515713629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212492880502290062020951505 159369660376717546515713629)
          ·
            refine ⟨59763622641269079943392611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159369660376717546515713629 59763622641269079943392611)
            ·
              refine ⟨89645433961903619915088917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59763622641269079943392611 89645433961903619915088917)
              ·
                refine ⟨4202129716964232183519793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 89645433961903619915088917 4202129716964232183519793)
                ·
                  refine ⟨3151597287723174137639845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4202129716964232183519793 3151597287723174137639845)
                  ·
                    refine ⟨590924491448095150807471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3151597287723174137639845 590924491448095150807471)
                    ·
                      rfl

theorem cell23_3452464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 6, 2, 4].length) (baseStart_3452464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452464 prefixEnd_3452464 := by exact prefixLift 3452464
  have htrace : WordTrace (prefixWord ++ tailWord_3452464) baseStart_3452464 baseEnd_3452464 := by
    simpa [prefixWord, tailWord_3452464, baseEnd_3452464] using wordTrace_append hprefix tailTrace_3452464
  have hstable : (prefixWord ++ tailWord_3452464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452464).length < 2 ^ (prefixWord ++ tailWord_3452464).sum := by decide
  have hdescent : baseEnd_3452464 < baseStart_3452464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452467 : List Nat := [1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 6]
def baseStart_3452467 : Nat := 118140960795 + 3452467 * 2 ^ 59
def prefixEnd_3452467 : Nat := 4983230072969 + 3 ^ 40 * 3452467 * 2
def baseEnd_3452467 : Nat := 1772775014786248940684899

theorem tailTrace_3452467 : CollatzResearch.WordTrace tailWord_3452467 prefixEnd_3452467 1772775014786248940684899 := by
  unfold tailWord_3452467
  simp only [CollatzResearch.WordTrace]
  refine ⟨125921816383309168265515655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83947877588872778843677103 125921816383309168265515655)
  ·
    refine ⟨188882724574963752398273483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125921816383309168265515655 188882724574963752398273483)
    ·
      refine ⟨283324086862445628597410225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188882724574963752398273483 283324086862445628597410225)
      ·
        refine ⟨212493065146834221448057669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283324086862445628597410225 212493065146834221448057669)
        ·
          refine ⟨39842449715031416521510813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212493065146834221448057669 39842449715031416521510813)
          ·
            refine ⟨14940918643136781195566555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39842449715031416521510813 14940918643136781195566555)
            ·
              refine ⟨22411377964705171793349833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14940918643136781195566555 22411377964705171793349833)
              ·
                refine ⟨16808533473528878845012375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22411377964705171793349833 16808533473528878845012375)
                ·
                  refine ⟨25212800210293318267518563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16808533473528878845012375 25212800210293318267518563)
                  ·
                    refine ⟨37819200315439977401277845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25212800210293318267518563 37819200315439977401277845)
                    ·
                      refine ⟨1772775014786248940684899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37819200315439977401277845 1772775014786248940684899)
                      ·
                        rfl

theorem cell23_3452467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 6].length) (baseStart_3452467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452467 prefixEnd_3452467 := by exact prefixLift 3452467
  have htrace : WordTrace (prefixWord ++ tailWord_3452467) baseStart_3452467 baseEnd_3452467 := by
    simpa [prefixWord, tailWord_3452467, baseEnd_3452467] using wordTrace_append hprefix tailTrace_3452467
  have hstable : (prefixWord ++ tailWord_3452467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452467).length < 2 ^ (prefixWord ++ tailWord_3452467).sum := by decide
  have hdescent : baseEnd_3452467 < baseStart_3452467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452474 : List Nat := [3, 1, 1, 1, 3, 2, 2, 2, 3, 2, 3]
def baseStart_3452474 : Nat := 118140960795 + 3452474 * 2 ^ 59
def prefixEnd_3452474 : Nat := 4983230072969 + 3 ^ 40 * 3452474 * 2
def baseEnd_3452474 : Nat := 1772778609150830413297367

theorem tailTrace_3452474 : CollatzResearch.WordTrace tailWord_3452474 prefixEnd_3452474 1772778609150830413297367 := by
  unfold tailWord_3452474
  simp only [CollatzResearch.WordTrace]
  refine ⟨31480517923570952115255119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83948047796189205640680317 31480517923570952115255119)
  ·
    refine ⟨47220776885356428172882679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31480517923570952115255119 47220776885356428172882679)
    ·
      refine ⟨70831165328034642259324019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47220776885356428172882679 70831165328034642259324019)
      ·
        refine ⟨106246747992051963388986029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70831165328034642259324019 106246747992051963388986029)
        ·
          refine ⟨39842530497019486270869761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106246747992051963388986029 39842530497019486270869761)
          ·
            refine ⟨29881897872764614703152321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39842530497019486270869761 29881897872764614703152321)
            ·
              refine ⟨22411423404573461027364241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29881897872764614703152321 22411423404573461027364241)
              ·
                refine ⟨16808567553430095770523181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22411423404573461027364241 16808567553430095770523181)
                ·
                  refine ⟨6303212832536285913946193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16808567553430095770523181 6303212832536285913946193)
                  ·
                    refine ⟨4727409624402214435459645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6303212832536285913946193 4727409624402214435459645)
                    ·
                      refine ⟨1772778609150830413297367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4727409624402214435459645 1772778609150830413297367)
                      ·
                        rfl

theorem cell23_3452474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 3, 2, 3].length) (baseStart_3452474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452474 prefixEnd_3452474 := by exact prefixLift 3452474
  have htrace : WordTrace (prefixWord ++ tailWord_3452474) baseStart_3452474 baseEnd_3452474 := by
    simpa [prefixWord, tailWord_3452474, baseEnd_3452474] using wordTrace_append hprefix tailTrace_3452474
  have hstable : (prefixWord ++ tailWord_3452474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452474).length < 2 ^ (prefixWord ++ tailWord_3452474).sum := by decide
  have hdescent : baseEnd_3452474 < baseStart_3452474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452481 : List Nat := [1, 2, 5, 1, 1, 1, 3, 3, 2, 4]
def baseStart_3452481 : Nat := 118140960795 + 3452481 * 2 ^ 59
def prefixEnd_3452481 : Nat := 4983230072969 + 3 ^ 40 * 3452481 * 2
def baseEnd_3452481 : Nat := 590927401171803961969945

theorem tailTrace_3452481 : CollatzResearch.WordTrace tailWord_3452481 prefixEnd_3452481 590927401171803961969945 := by
  unfold tailWord_3452481
  simp only [CollatzResearch.WordTrace]
  refine ⟨125922327005258448656525297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83948218003505632437683531 125922327005258448656525297)
  ·
    refine ⟨94441745253943836492393973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125922327005258448656525297 94441745253943836492393973)
    ·
      refine ⟨8853913617557234671161935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94441745253943836492393973 8853913617557234671161935)
      ·
        refine ⟨13280870426335852006742903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8853913617557234671161935 13280870426335852006742903)
        ·
          refine ⟨19921305639503778010114355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13280870426335852006742903 19921305639503778010114355)
          ·
            refine ⟨29881958459255667015171533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19921305639503778010114355 29881958459255667015171533)
            ·
              refine ⟨11205734422220875130689325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29881958459255667015171533 11205734422220875130689325)
              ·
                refine ⟨4202150408332828174008497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11205734422220875130689325 4202150408332828174008497)
                ·
                  refine ⟨3151612806249621130506373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4202150408332828174008497 3151612806249621130506373)
                  ·
                    refine ⟨590927401171803961969945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3151612806249621130506373 590927401171803961969945)
                    ·
                      rfl

theorem cell23_3452481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_3452481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452481 prefixEnd_3452481 := by exact prefixLift 3452481
  have htrace : WordTrace (prefixWord ++ tailWord_3452481) baseStart_3452481 baseEnd_3452481 := by
    simpa [prefixWord, tailWord_3452481, baseEnd_3452481] using wordTrace_append hprefix tailTrace_3452481
  have hstable : (prefixWord ++ tailWord_3452481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452481).length < 2 ^ (prefixWord ++ tailWord_3452481).sum := by decide
  have hdescent : baseEnd_3452481 < baseStart_3452481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452502 : List Nat := [5, 2, 2, 2, 1, 1, 3, 1, 1, 5]
def baseStart_3452502 : Nat := 118140960795 + 3452502 * 2 ^ 59
def prefixEnd_3452502 : Nat := 4983230072969 + 3 ^ 40 * 3452502 * 2
def baseEnd_3452502 : Nat := 590930995536385434582413

theorem tailTrace_3452502 : CollatzResearch.WordTrace tailWord_3452502 prefixEnd_3452502 590930995536385434582413 := by
  unfold tailWord_3452502
  simp only [CollatzResearch.WordTrace]
  refine ⟨7870193308636398077689985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83948728625454912828693173 7870193308636398077689985)
  ·
    refine ⟨5902644981477298558267489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7870193308636398077689985 5902644981477298558267489)
    ·
      refine ⟨4426983736107973918700617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5902644981477298558267489 4426983736107973918700617)
      ·
        refine ⟨3320237802080980439025463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4426983736107973918700617 3320237802080980439025463)
        ·
          refine ⟨4980356703121470658538195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3320237802080980439025463 4980356703121470658538195)
          ·
            refine ⟨7470535054682205987807293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4980356703121470658538195 7470535054682205987807293)
            ·
              refine ⟨2801450645505827245427735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7470535054682205987807293 2801450645505827245427735)
              ·
                refine ⟨4202175968258740868141603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2801450645505827245427735 4202175968258740868141603)
                ·
                  refine ⟨6303263952388111302212405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4202175968258740868141603 6303263952388111302212405)
                  ·
                    refine ⟨590930995536385434582413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6303263952388111302212405 590930995536385434582413)
                    ·
                      rfl

theorem cell23_3452502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_3452502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452502 prefixEnd_3452502 := by exact prefixLift 3452502
  have htrace : WordTrace (prefixWord ++ tailWord_3452502) baseStart_3452502 baseEnd_3452502 := by
    simpa [prefixWord, tailWord_3452502, baseEnd_3452502] using wordTrace_append hprefix tailTrace_3452502
  have hstable : (prefixWord ++ tailWord_3452502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452502).length < 2 ^ (prefixWord ++ tailWord_3452502).sum := by decide
  have hdescent : baseEnd_3452502 < baseStart_3452502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452521 : List Nat := [1, 2, 1, 1, 1, 4, 3, 4, 2, 1, 3]
def baseStart_3452521 : Nat := 118140960795 + 3452521 * 2 ^ 59
def prefixEnd_3452521 : Nat := 4983230072969 + 3 ^ 40 * 3452521 * 2
def baseEnd_3452521 : Nat := 1772802742741591729409651

theorem tailTrace_3452521 : CollatzResearch.WordTrace tailWord_3452521 prefixEnd_3452521 1772802742741591729409651 := by
  unfold tailWord_3452521
  simp only [CollatzResearch.WordTrace]
  refine ⟨125923785925113535487981417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83949190616742356991987611 125923785925113535487981417)
  ·
    refine ⟨94442839443835151615986063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125923785925113535487981417 94442839443835151615986063)
    ·
      refine ⟨141664259165752727423979095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94442839443835151615986063 141664259165752727423979095)
      ·
        refine ⟨212496388748629091135968643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141664259165752727423979095 212496388748629091135968643)
        ·
          refine ⟨318744583122943636703952965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212496388748629091135968643 318744583122943636703952965)
          ·
            refine ⟨59764609335551931881991181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 318744583122943636703952965 59764609335551931881991181)
            ·
              refine ⟨22411728500831974455746693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59764609335551931881991181 22411728500831974455746693)
              ·
                refine ⟨4202199093905995210452505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22411728500831974455746693 4202199093905995210452505)
                ·
                  refine ⟨3151649320429496407839379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4202199093905995210452505 3151649320429496407839379)
                  ·
                    refine ⟨4727473980644244611759069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3151649320429496407839379 4727473980644244611759069)
                    ·
                      refine ⟨1772802742741591729409651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4727473980644244611759069 1772802742741591729409651)
                      ·
                        rfl

theorem cell23_3452521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 4, 2, 1, 3].length) (baseStart_3452521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452521 prefixEnd_3452521 := by exact prefixLift 3452521
  have htrace : WordTrace (prefixWord ++ tailWord_3452521) baseStart_3452521 baseEnd_3452521 := by
    simpa [prefixWord, tailWord_3452521, baseEnd_3452521] using wordTrace_append hprefix tailTrace_3452521
  have hstable : (prefixWord ++ tailWord_3452521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452521).length < 2 ^ (prefixWord ++ tailWord_3452521).sum := by decide
  have hdescent : baseEnd_3452521 < baseStart_3452521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452522 : List Nat := [3, 1, 3, 2, 1, 2, 4, 2, 1, 2, 2]
def baseStart_3452522 : Nat := 118140960795 + 3452522 * 2 ^ 59
def prefixEnd_3452522 : Nat := 4983230072969 + 3 ^ 40 * 3452522 * 2
def baseEnd_3452522 : Nat := 1772803256222246225497147

theorem tailTrace_3452522 : CollatzResearch.WordTrace tailWord_3452522 prefixEnd_3452522 1772803256222246225497147 := by
  unfold tailWord_3452522
  simp only [CollatzResearch.WordTrace]
  refine ⟨31480955599527478164691955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83949214932073275105845213 31480955599527478164691955)
  ·
    refine ⟨47221433399291217247037933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31480955599527478164691955 47221433399291217247037933)
    ·
      refine ⟨17708037524734206467639225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47221433399291217247037933 17708037524734206467639225)
      ·
        refine ⟨13281028143550654850729419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17708037524734206467639225 13281028143550654850729419)
        ·
          refine ⟨19921542215325982276094129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13281028143550654850729419 19921542215325982276094129)
          ·
            refine ⟨14941156661494486707070597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19921542215325982276094129 14941156661494486707070597)
            ·
              refine ⟨2801466874030216257575737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14941156661494486707070597 2801466874030216257575737)
              ·
                refine ⟨2101100155522662193181803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2801466874030216257575737 2101100155522662193181803)
                ·
                  refine ⟨3151650233283993289772705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2101100155522662193181803 3151650233283993289772705)
                  ·
                    refine ⟨2363737674962994967329529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3151650233283993289772705 2363737674962994967329529)
                    ·
                      refine ⟨1772803256222246225497147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2363737674962994967329529 1772803256222246225497147)
                      ·
                        rfl

theorem cell23_3452522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_3452522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452522 prefixEnd_3452522 := by exact prefixLift 3452522
  have htrace : WordTrace (prefixWord ++ tailWord_3452522) baseStart_3452522 baseEnd_3452522 := by
    simpa [prefixWord, tailWord_3452522, baseEnd_3452522] using wordTrace_append hprefix tailTrace_3452522
  have hstable : (prefixWord ++ tailWord_3452522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452522).length < 2 ^ (prefixWord ++ tailWord_3452522).sum := by decide
  have hdescent : baseEnd_3452522 < baseStart_3452522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452572 : List Nat := [2, 2, 3, 2, 4, 1, 1, 2, 2, 1, 3]
def baseStart_3452572 : Nat := 118140960795 + 3452572 * 2 ^ 59
def prefixEnd_3452572 : Nat := 4983230072969 + 3 ^ 40 * 3452572 * 2
def baseEnd_3452572 : Nat := 1772828930254971029871917

theorem tailTrace_3452572 : CollatzResearch.WordTrace tailWord_3452572 prefixEnd_3452572 1772828930254971029871917 := by
  unfold tailWord_3452572
  simp only [CollatzResearch.WordTrace]
  refine ⟨62962823023964385599043985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83950430698619180798725313 62962823023964385599043985)
  ·
    refine ⟨47222117267973289199282989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62962823023964385599043985 47222117267973289199282989)
    ·
      refine ⟨17708293975489983449731121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47222117267973289199282989 17708293975489983449731121)
      ·
        refine ⟨13281220481617487587298341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17708293975489983449731121 13281220481617487587298341)
        ·
          refine ⟨2490228840303278922618439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13281220481617487587298341 2490228840303278922618439)
          ·
            refine ⟨3735343260454918383927659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2490228840303278922618439 3735343260454918383927659)
            ·
              refine ⟨5603014890682377575891489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3735343260454918383927659 5603014890682377575891489)
              ·
                refine ⟨4202261168011783181918617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5603014890682377575891489 4202261168011783181918617)
                ·
                  refine ⟨3151695876008837386438963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4202261168011783181918617 3151695876008837386438963)
                  ·
                    refine ⟨4727543814013256079658445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3151695876008837386438963 4727543814013256079658445)
                    ·
                      refine ⟨1772828930254971029871917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4727543814013256079658445 1772828930254971029871917)
                      ·
                        rfl

theorem cell23_3452572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_3452572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452572 prefixEnd_3452572 := by exact prefixLift 3452572
  have htrace : WordTrace (prefixWord ++ tailWord_3452572) baseStart_3452572 baseEnd_3452572 := by
    simpa [prefixWord, tailWord_3452572, baseEnd_3452572] using wordTrace_append hprefix tailTrace_3452572
  have hstable : (prefixWord ++ tailWord_3452572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452572).length < 2 ^ (prefixWord ++ tailWord_3452572).sum := by decide
  have hdescent : baseEnd_3452572 < baseStart_3452572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452595 : List Nat := [1, 1, 1, 2, 3, 3, 5, 1, 2, 2, 2]
def baseStart_3452595 : Nat := 118140960795 + 3452595 * 2 ^ 59
def prefixEnd_3452595 : Nat := 4983230072969 + 3 ^ 40 * 3452595 * 2
def baseEnd_3452595 : Nat := 1772840740310024439884311

theorem tailTrace_3452595 : CollatzResearch.WordTrace tailWord_3452595 prefixEnd_3452595 1772840740310024439884311 := by
  unfold tailWord_3452595
  simp only [CollatzResearch.WordTrace]
  refine ⟨125926484926845446126175239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83950989951230297417450159 125926484926845446126175239)
  ·
    refine ⟨188889727390268169189262859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125926484926845446126175239 188889727390268169189262859)
    ·
      refine ⟨283334591085402253783894289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188889727390268169189262859 283334591085402253783894289)
      ·
        refine ⟨212500943314051690337920717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283334591085402253783894289 212500943314051690337920717)
        ·
          refine ⟨79687853742769383876720269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212500943314051690337920717 79687853742769383876720269)
          ·
            refine ⟨29882945153538518953770101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79687853742769383876720269 29882945153538518953770101)
            ·
              refine ⟨2801526108144236151915947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29882945153538518953770101 2801526108144236151915947)
              ·
                refine ⟨4202289162216354227873921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2801526108144236151915947 4202289162216354227873921)
                ·
                  refine ⟨3151716871662265670905441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4202289162216354227873921 3151716871662265670905441)
                  ·
                    refine ⟨2363787653746699253179081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3151716871662265670905441 2363787653746699253179081)
                    ·
                      refine ⟨1772840740310024439884311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2363787653746699253179081 1772840740310024439884311)
                      ·
                        rfl

theorem cell23_3452595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 1, 2, 2, 2].length) (baseStart_3452595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452595 prefixEnd_3452595 := by exact prefixLift 3452595
  have htrace : WordTrace (prefixWord ++ tailWord_3452595) baseStart_3452595 baseEnd_3452595 := by
    simpa [prefixWord, tailWord_3452595, baseEnd_3452595] using wordTrace_append hprefix tailTrace_3452595
  have hstable : (prefixWord ++ tailWord_3452595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452595).length < 2 ^ (prefixWord ++ tailWord_3452595).sum := by decide
  have hdescent : baseEnd_3452595 < baseStart_3452595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452641 : List Nat := [1, 2, 3, 1, 5, 1, 1, 1, 1, 2, 5]
def baseStart_3452641 : Nat := 118140960795 + 3452641 * 2 ^ 59
def prefixEnd_3452641 : Nat := 4983230072969 + 3 ^ 40 * 3452641 * 2
def baseEnd_3452641 : Nat := 1772864360420131259909099

theorem tailTrace_3452641 : CollatzResearch.WordTrace tailWord_3452641 prefixEnd_3452641 1772864360420131259909099 := by
  unfold tailWord_3452641
  simp only [CollatzResearch.WordTrace]
  refine ⟨125928162684678795982349777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83952108456452530654899851 125928162684678795982349777)
  ·
    refine ⟨94446122013509096986762333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125928162684678795982349777 94446122013509096986762333)
    ·
      refine ⟨35417295755065911370035875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94446122013509096986762333 35417295755065911370035875)
      ·
        refine ⟨53125943632598867055053813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35417295755065911370035875 53125943632598867055053813)
        ·
          refine ⟨4980557215556143786411295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53125943632598867055053813 4980557215556143786411295)
          ·
            refine ⟨7470835823334215679616943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4980557215556143786411295 7470835823334215679616943)
            ·
              refine ⟨11206253735001323519425415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7470835823334215679616943 11206253735001323519425415)
              ·
                refine ⟨16809380602501985279138123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11206253735001323519425415 16809380602501985279138123)
                ·
                  refine ⟨25214070903752977918707185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16809380602501985279138123 25214070903752977918707185)
                  ·
                    refine ⟨18910553177814733439030389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25214070903752977918707185 18910553177814733439030389)
                    ·
                      refine ⟨1772864360420131259909099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18910553177814733439030389 1772864360420131259909099)
                      ·
                        rfl

theorem cell23_3452641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 2, 5].length) (baseStart_3452641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452641 prefixEnd_3452641 := by exact prefixLift 3452641
  have htrace : WordTrace (prefixWord ++ tailWord_3452641) baseStart_3452641 baseEnd_3452641 := by
    simpa [prefixWord, tailWord_3452641, baseEnd_3452641] using wordTrace_append hprefix tailTrace_3452641
  have hstable : (prefixWord ++ tailWord_3452641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452641).length < 2 ^ (prefixWord ++ tailWord_3452641).sum := by decide
  have hdescent : baseEnd_3452641 < baseStart_3452641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452651 : List Nat := [1, 1, 1, 1, 2, 4, 2, 3, 2, 4, 2]
def baseStart_3452651 : Nat := 118140960795 + 3452651 * 2 ^ 59
def prefixEnd_3452651 : Nat := 4983230072969 + 3 ^ 40 * 3452651 * 2
def baseEnd_3452651 : Nat := 1772869495226676220784053

theorem tailTrace_3452651 : CollatzResearch.WordTrace tailWord_3452651 prefixEnd_3452651 1772869495226676220784053 := by
  unfold tailWord_3452651
  simp only [CollatzResearch.WordTrace]
  refine ⟨125928527414642567690213807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83952351609761711793475871 125928527414642567690213807)
  ·
    refine ⟨188892791121963851535320711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125928527414642567690213807 188892791121963851535320711)
    ·
      refine ⟨283339186682945777302981067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188892791121963851535320711 283339186682945777302981067)
      ·
        refine ⟨425008780024418665954471601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283339186682945777302981067 425008780024418665954471601)
        ·
          refine ⟨318756585018313999465853701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 425008780024418665954471601 318756585018313999465853701)
          ·
            refine ⟨59766859690933874899847569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 318756585018313999465853701 59766859690933874899847569)
            ·
              refine ⟨44825144768200406174885677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59766859690933874899847569 44825144768200406174885677)
              ·
                refine ⟨16809429288075152315582129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44825144768200406174885677 16809429288075152315582129)
                ·
                  refine ⟨12607071966056364236686597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16809429288075152315582129 12607071966056364236686597)
                  ·
                    refine ⟨2363825993635568294378737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12607071966056364236686597 2363825993635568294378737)
                    ·
                      refine ⟨1772869495226676220784053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2363825993635568294378737 1772869495226676220784053)
                      ·
                        rfl

theorem cell23_3452651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 4, 2].length) (baseStart_3452651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452651 prefixEnd_3452651 := by exact prefixLift 3452651
  have htrace : WordTrace (prefixWord ++ tailWord_3452651) baseStart_3452651 baseEnd_3452651 := by
    simpa [prefixWord, tailWord_3452651, baseEnd_3452651] using wordTrace_append hprefix tailTrace_3452651
  have hstable : (prefixWord ++ tailWord_3452651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452651).length < 2 ^ (prefixWord ++ tailWord_3452651).sum := by decide
  have hdescent : baseEnd_3452651 < baseStart_3452651 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452671 : List Nat := [1, 1, 2, 2, 1, 3, 3, 3, 2, 2, 3]
def baseStart_3452671 : Nat := 118140960795 + 3452671 * 2 ^ 59
def prefixEnd_3452671 : Nat := 4983230072969 + 3 ^ 40 * 3452671 * 2
def baseEnd_3452671 : Nat := 1772879764839766142533961

theorem tailTrace_3452671 : CollatzResearch.WordTrace tailWord_3452671 prefixEnd_3452671 1772879764839766142533961 := by
  unfold tailWord_3452671
  simp only [CollatzResearch.WordTrace]
  refine ⟨125929256874570111105941867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83952837916380074070627911 125929256874570111105941867)
  ·
    refine ⟨188893885311855166658912801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125929256874570111105941867 188893885311855166658912801)
    ·
      refine ⟨141670413983891374994184601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188893885311855166658912801 141670413983891374994184601)
      ·
        refine ⟨106252810487918531245638451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141670413983891374994184601 106252810487918531245638451)
        ·
          refine ⟨159379215731877796868457677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106252810487918531245638451 159379215731877796868457677)
          ·
            refine ⟨59767205899454173825671629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159379215731877796868457677 59767205899454173825671629)
            ·
              refine ⟨22412702212295315184626861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59767205899454173825671629 22412702212295315184626861)
              ·
                refine ⟨8404763329610743194235073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22412702212295315184626861 8404763329610743194235073)
                ·
                  refine ⟨6303572497208057395676305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8404763329610743194235073 6303572497208057395676305)
                  ·
                    refine ⟨4727679372906043046757229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6303572497208057395676305 4727679372906043046757229)
                    ·
                      refine ⟨1772879764839766142533961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4727679372906043046757229 1772879764839766142533961)
                      ·
                        rfl

theorem cell23_3452671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 2, 2, 3].length) (baseStart_3452671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452671 prefixEnd_3452671 := by exact prefixLift 3452671
  have htrace : WordTrace (prefixWord ++ tailWord_3452671) baseStart_3452671 baseEnd_3452671 := by
    simpa [prefixWord, tailWord_3452671, baseEnd_3452671] using wordTrace_append hprefix tailTrace_3452671
  have hstable : (prefixWord ++ tailWord_3452671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452671).length < 2 ^ (prefixWord ++ tailWord_3452671).sum := by decide
  have hdescent : baseEnd_3452671 < baseStart_3452671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452695 : List Nat := [1, 1, 3, 4, 2, 2, 1, 4, 1, 4]
def baseStart_3452695 : Nat := 118140960795 + 3452695 * 2 ^ 59
def prefixEnd_3452695 : Nat := 4983230072969 + 3 ^ 40 * 3452695 * 2
def baseEnd_3452695 : Nat := 590964029458491349544617

theorem tailTrace_3452695 : CollatzResearch.WordTrace tailWord_3452695 prefixEnd_3452695 590964029458491349544617 := by
  unfold tailWord_3452695
  simp only [CollatzResearch.WordTrace]
  refine ⟨125930132226483163204815539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83953421484322108803210359 125930132226483163204815539)
  ·
    refine ⟨188895198339724744807223309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125930132226483163204815539 188895198339724744807223309)
    ·
      refine ⟨70835699377396779302708741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188895198339724744807223309 70835699377396779302708741)
      ·
        refine ⟨13281693633261896119257889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70835699377396779302708741 13281693633261896119257889)
        ·
          refine ⟨9961270224946422089443417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13281693633261896119257889 9961270224946422089443417)
          ·
            refine ⟨7470952668709816567082563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9961270224946422089443417 7470952668709816567082563)
            ·
              refine ⟨11206429003064724850623845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7470952668709816567082563 11206429003064724850623845)
              ·
                refine ⟨2101205438074635909491971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11206429003064724850623845 2101205438074635909491971)
                ·
                  refine ⟨3151808157111953864237957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2101205438074635909491971 3151808157111953864237957)
                  ·
                    refine ⟨590964029458491349544617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3151808157111953864237957 590964029458491349544617)
                    ·
                      rfl

theorem cell23_3452695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 4, 1, 4].length) (baseStart_3452695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452695 prefixEnd_3452695 := by exact prefixLift 3452695
  have htrace : WordTrace (prefixWord ++ tailWord_3452695) baseStart_3452695 baseEnd_3452695 := by
    simpa [prefixWord, tailWord_3452695, baseEnd_3452695] using wordTrace_append hprefix tailTrace_3452695
  have hstable : (prefixWord ++ tailWord_3452695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452695).length < 2 ^ (prefixWord ++ tailWord_3452695).sum := by decide
  have hdescent : baseEnd_3452695 < baseStart_3452695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452721 : List Nat := [1, 2, 2, 3, 2, 2, 2, 1, 3, 5]
def baseStart_3452721 : Nat := 118140960795 + 3452721 * 2 ^ 59
def prefixEnd_3452721 : Nat := 4983230072969 + 3 ^ 40 * 3452721 * 2
def baseEnd_3452721 : Nat := 590968479624163648969577

theorem tailTrace_3452721 : CollatzResearch.WordTrace tailWord_3452721 prefixEnd_3452721 590968479624163648969577 := by
  unfold tailWord_3452721
  simp only [CollatzResearch.WordTrace]
  refine ⟨125931080524388969645262017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83954053682925979763508011 125931080524388969645262017)
  ·
    refine ⟨94448310393291727233946513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125931080524388969645262017 94448310393291727233946513)
    ·
      refine ⟨70836232794968795425459885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94448310393291727233946513 70836232794968795425459885)
      ·
        refine ⟨26563587298113298284547457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70836232794968795425459885 26563587298113298284547457)
        ·
          refine ⟨19922690473584973713410593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26563587298113298284547457 19922690473584973713410593)
          ·
            refine ⟨14942017855188730285057945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19922690473584973713410593 14942017855188730285057945)
            ·
              refine ⟨11206513391391547713793459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14942017855188730285057945 11206513391391547713793459)
              ·
                refine ⟨16809770087087321570690189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11206513391391547713793459 16809770087087321570690189)
                ·
                  refine ⟨6303663782657745589008821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16809770087087321570690189 6303663782657745589008821)
                  ·
                    refine ⟨590968479624163648969577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6303663782657745589008821 590968479624163648969577)
                    ·
                      rfl

theorem cell23_3452721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 3, 5].length) (baseStart_3452721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452721 prefixEnd_3452721 := by exact prefixLift 3452721
  have htrace : WordTrace (prefixWord ++ tailWord_3452721) baseStart_3452721 baseEnd_3452721 := by
    simpa [prefixWord, tailWord_3452721, baseEnd_3452721] using wordTrace_append hprefix tailTrace_3452721
  have hstable : (prefixWord ++ tailWord_3452721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452721).length < 2 ^ (prefixWord ++ tailWord_3452721).sum := by decide
  have hdescent : baseEnd_3452721 < baseStart_3452721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452728 : List Nat := [2, 1, 2, 1, 3, 4, 1, 1, 1, 5, 2]
def baseStart_3452728 : Nat := 118140960795 + 3452728 * 2 ^ 59
def prefixEnd_3452728 : Nat := 4983230072969 + 3 ^ 40 * 3452728 * 2
def baseEnd_3452728 : Nat := 1772909033237072419521199

theorem tailTrace_3452728 : CollatzResearch.WordTrace tailWord_3452728 prefixEnd_3452728 1772909033237072419521199 := by
  unfold tailWord_3452728
  simp only [CollatzResearch.WordTrace]
  refine ⟨62965667917681804920383419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83954223890242406560511225 62965667917681804920383419)
  ·
    refine ⟨94448501876522707380575129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62965667917681804920383419 94448501876522707380575129)
    ·
      refine ⟨70836376407392030535431347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94448501876522707380575129 70836376407392030535431347)
      ·
        refine ⟨106254564611088045803147021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70836376407392030535431347 106254564611088045803147021)
        ·
          refine ⟨39845461729158017176180133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106254564611088045803147021 39845461729158017176180133)
          ·
            refine ⟨7471024074217128220533775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39845461729158017176180133 7471024074217128220533775)
            ·
              refine ⟨11206536111325692330800663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7471024074217128220533775 11206536111325692330800663)
              ·
                refine ⟨16809804166988538496200995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11206536111325692330800663 16809804166988538496200995)
                ·
                  refine ⟨25214706250482807744301493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16809804166988538496200995 25214706250482807744301493)
                  ·
                    refine ⟨2363878710982763226028265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25214706250482807744301493 2363878710982763226028265)
                    ·
                      refine ⟨1772909033237072419521199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2363878710982763226028265 1772909033237072419521199)
                      ·
                        rfl

theorem cell23_3452728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 1, 5, 2].length) (baseStart_3452728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452728 prefixEnd_3452728 := by exact prefixLift 3452728
  have htrace : WordTrace (prefixWord ++ tailWord_3452728) baseStart_3452728 baseEnd_3452728 := by
    simpa [prefixWord, tailWord_3452728, baseEnd_3452728] using wordTrace_append hprefix tailTrace_3452728
  have hstable : (prefixWord ++ tailWord_3452728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452728).length < 2 ^ (prefixWord ++ tailWord_3452728).sum := by decide
  have hdescent : baseEnd_3452728 < baseStart_3452728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452742 : List Nat := [6, 1, 1, 2, 1, 3, 1, 2, 6]
def baseStart_3452742 : Nat := 118140960795 + 3452742 * 2 ^ 59
def prefixEnd_3452742 : Nat := 4983230072969 + 3 ^ 40 * 3452742 * 2
def baseEnd_3452742 : Nat := 196990691329581707194015

theorem tailTrace_3452742 : CollatzResearch.WordTrace tailWord_3452742 prefixEnd_3452742 196990691329581707194015 := by
  unfold tailWord_3452742
  simp only [CollatzResearch.WordTrace]
  refine ⟨3935370201791027819743015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 83954564304875260154517653 3935370201791027819743015)
  ·
    refine ⟨5903055302686541729614523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3935370201791027819743015 5903055302686541729614523)
    ·
      refine ⟨8854582954029812594421785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5903055302686541729614523 8854582954029812594421785)
      ·
        refine ⟨6640937215522359445816339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8854582954029812594421785 6640937215522359445816339)
        ·
          refine ⟨9961405823283539168724509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6640937215522359445816339 9961405823283539168724509)
          ·
            refine ⟨3735527183731327188271691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9961405823283539168724509 3735527183731327188271691)
            ·
              refine ⟨5603290775596990782407537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3735527183731327188271691 5603290775596990782407537)
              ·
                refine ⟨4202468081697743086805653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5603290775596990782407537 4202468081697743086805653)
                ·
                  refine ⟨196990691329581707194015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4202468081697743086805653 196990691329581707194015)
                  ·
                    rfl

theorem cell23_3452742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_3452742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452742 prefixEnd_3452742 := by exact prefixLift 3452742
  have htrace : WordTrace (prefixWord ++ tailWord_3452742) baseStart_3452742 baseEnd_3452742 := by
    simpa [prefixWord, tailWord_3452742, baseEnd_3452742] using wordTrace_append hprefix tailTrace_3452742
  have hstable : (prefixWord ++ tailWord_3452742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452742).length < 2 ^ (prefixWord ++ tailWord_3452742).sum := by decide
  have hdescent : baseEnd_3452742 < baseStart_3452742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452761 : List Nat := [1, 2, 1, 2, 2, 3, 3, 2, 1, 1, 5]
def baseStart_3452761 : Nat := 118140960795 + 3452761 * 2 ^ 59
def prefixEnd_3452761 : Nat := 4983230072969 + 3 ^ 40 * 3452761 * 2
def baseEnd_3452761 : Nat := 1772925978098670790408547

theorem tailTrace_3452761 : CollatzResearch.WordTrace tailWord_3452761 prefixEnd_3452761 1772925978098670790408547 := by
  unfold tailWord_3452761
  simp only [CollatzResearch.WordTrace]
  refine ⟨125932539444244056476718137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83955026296162704317812091 125932539444244056476718137)
  ·
    refine ⟨94449404583183042357538603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125932539444244056476718137 94449404583183042357538603)
    ·
      refine ⟨141674106874774563536307905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94449404583183042357538603 141674106874774563536307905)
      ·
        refine ⟨106255580156080922652230929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141674106874774563536307905 106255580156080922652230929)
        ·
          refine ⟨79691685117060691989173197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106255580156080922652230929 79691685117060691989173197)
          ·
            refine ⟨29884381918897759495939949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79691685117060691989173197 29884381918897759495939949)
            ·
              refine ⟨11206643219586659810977481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29884381918897759495939949 11206643219586659810977481)
              ·
                refine ⟨8404982414689994858233111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11206643219586659810977481 8404982414689994858233111)
                ·
                  refine ⟨12607473622034992287349667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8404982414689994858233111 12607473622034992287349667)
                  ·
                    refine ⟨18911210433052488431024501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12607473622034992287349667 18911210433052488431024501)
                    ·
                      refine ⟨1772925978098670790408547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18911210433052488431024501 1772925978098670790408547)
                      ·
                        rfl

theorem cell23_3452761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 1, 5].length) (baseStart_3452761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452761 prefixEnd_3452761 := by exact prefixLift 3452761
  have htrace : WordTrace (prefixWord ++ tailWord_3452761) baseStart_3452761 baseEnd_3452761 := by
    simpa [prefixWord, tailWord_3452761, baseEnd_3452761] using wordTrace_append hprefix tailTrace_3452761
  have hstable : (prefixWord ++ tailWord_3452761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452761).length < 2 ^ (prefixWord ++ tailWord_3452761).sum := by decide
  have hdescent : baseEnd_3452761 < baseStart_3452761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452768 : List Nat := [2, 1, 1, 3, 3, 4, 1, 1, 1, 6]
def baseStart_3452768 : Nat := 118140960795 + 3452768 * 2 ^ 59
def prefixEnd_3452768 : Nat := 4983230072969 + 3 ^ 40 * 3452768 * 2
def baseEnd_3452768 : Nat := 590976524154417421007005

theorem tailTrace_3452768 : CollatzResearch.WordTrace tailWord_3452768 prefixEnd_3452768 590976524154417421007005 := by
  unfold tailWord_3452768
  simp only [CollatzResearch.WordTrace]
  refine ⟨62966397377609348336111479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83955196503479131114815305 62966397377609348336111479)
  ·
    refine ⟨94449596066414022504167219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62966397377609348336111479 94449596066414022504167219)
    ·
      refine ⟨141674394099621033756250829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94449596066414022504167219 141674394099621033756250829)
      ·
        refine ⟨53127897787357887658594061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141674394099621033756250829 53127897787357887658594061)
        ·
          refine ⟨19922961670259207871972773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53127897787357887658594061 19922961670259207871972773)
          ·
            refine ⟨3735555313173601475994895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19922961670259207871972773 3735555313173601475994895)
            ·
              refine ⟨5603332969760402213992343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3735555313173601475994895 5603332969760402213992343)
              ·
                refine ⟨8404999454640603320988515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5603332969760402213992343 8404999454640603320988515)
                ·
                  refine ⟨12607499181960904981482773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8404999454640603320988515 12607499181960904981482773)
                  ·
                    refine ⟨590976524154417421007005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12607499181960904981482773 590976524154417421007005)
                    ·
                      rfl

theorem cell23_3452768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 1, 6].length) (baseStart_3452768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452768 prefixEnd_3452768 := by exact prefixLift 3452768
  have htrace : WordTrace (prefixWord ++ tailWord_3452768) baseStart_3452768 baseEnd_3452768 := by
    simpa [prefixWord, tailWord_3452768, baseEnd_3452768] using wordTrace_append hprefix tailTrace_3452768
  have hstable : (prefixWord ++ tailWord_3452768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452768).length < 2 ^ (prefixWord ++ tailWord_3452768).sum := by decide
  have hdescent : baseEnd_3452768 < baseStart_3452768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452775 : List Nat := [1, 1, 5, 1, 2, 1, 1, 4, 3, 2, 2]
def baseStart_3452775 : Nat := 118140960795 + 3452775 * 2 ^ 59
def prefixEnd_3452775 : Nat := 4983230072969 + 3 ^ 40 * 3452775 * 2
def baseEnd_3452775 : Nat := 1772933166827833735633483

theorem tailTrace_3452775 : CollatzResearch.WordTrace tailWord_3452775 prefixEnd_3452775 1772933166827833735633483 := by
  unfold tailWord_3452775
  simp only [CollatzResearch.WordTrace]
  refine ⟨125933050066193336867727779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83955366710795557911818519 125933050066193336867727779)
  ·
    refine ⟨188899575099290005301591669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125933050066193336867727779 188899575099290005301591669)
    ·
      refine ⟨17709335165558437997024219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 188899575099290005301591669 17709335165558437997024219)
      ·
        refine ⟨26564002748337656995536329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17709335165558437997024219 26564002748337656995536329)
        ·
          refine ⟨19923002061253242746652247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26564002748337656995536329 19923002061253242746652247)
          ·
            refine ⟨29884503091879864119978371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19923002061253242746652247 29884503091879864119978371)
            ·
              refine ⟨44826754637819796179967557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29884503091879864119978371 44826754637819796179967557)
              ·
                refine ⟨8405016494591211783743917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44826754637819796179967557 8405016494591211783743917)
                ·
                  refine ⟨3151881185471704418903969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8405016494591211783743917 3151881185471704418903969)
                  ·
                    refine ⟨2363910889103778314177977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3151881185471704418903969 2363910889103778314177977)
                    ·
                      refine ⟨1772933166827833735633483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2363910889103778314177977 1772933166827833735633483)
                      ·
                        rfl

theorem cell23_3452775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 3, 2, 2].length) (baseStart_3452775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452775 prefixEnd_3452775 := by exact prefixLift 3452775
  have htrace : WordTrace (prefixWord ++ tailWord_3452775) baseStart_3452775 baseEnd_3452775 := by
    simpa [prefixWord, tailWord_3452775, baseEnd_3452775] using wordTrace_append hprefix tailTrace_3452775
  have hstable : (prefixWord ++ tailWord_3452775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452775).length < 2 ^ (prefixWord ++ tailWord_3452775).sum := by decide
  have hdescent : baseEnd_3452775 < baseStart_3452775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452798 : List Nat := [4, 2, 3, 1, 1, 1, 11]
def baseStart_3452798 : Nat := 118140960795 + 3452798 * 2 ^ 59
def prefixEnd_3452798 : Nat := 4983230072969 + 3 ^ 40 * 3452798 * 2
def baseEnd_3452798 : Nat := 21888209591146754884517

theorem tailTrace_3452798 : CollatzResearch.WordTrace tailWord_3452798 prefixEnd_3452798 21888209591146754884517 := by
  unfold tailWord_3452798
  simp only [CollatzResearch.WordTrace]
  refine ⟨15741736118138751474476881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83955925963406674530543365 15741736118138751474476881)
  ·
    refine ⟨11806302088604063605857661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15741736118138751474476881 11806302088604063605857661)
    ·
      refine ⟨4427363283226523852196623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11806302088604063605857661 4427363283226523852196623)
      ·
        refine ⟨6641044924839785778294935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4427363283226523852196623 6641044924839785778294935)
        ·
          refine ⟨9961567387259678667442403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6641044924839785778294935 9961567387259678667442403)
          ·
            refine ⟨14942351080889518001163605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9961567387259678667442403 14942351080889518001163605)
            ·
              refine ⟨21888209591146754884517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 14942351080889518001163605 21888209591146754884517)
              ·
                rfl

theorem cell23_3452798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 11].length) (baseStart_3452798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452798 prefixEnd_3452798 := by exact prefixLift 3452798
  have htrace : WordTrace (prefixWord ++ tailWord_3452798) baseStart_3452798 baseEnd_3452798 := by
    simpa [prefixWord, tailWord_3452798, baseEnd_3452798] using wordTrace_append hprefix tailTrace_3452798
  have hstable : (prefixWord ++ tailWord_3452798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452798).length < 2 ^ (prefixWord ++ tailWord_3452798).sum := by decide
  have hdescent : baseEnd_3452798 < baseStart_3452798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452809 : List Nat := [1, 2, 1, 1, 5, 1, 5, 2, 1, 2, 2]
def baseStart_3452809 : Nat := 118140960795 + 3452809 * 2 ^ 59
def prefixEnd_3452809 : Nat := 4983230072969 + 3 ^ 40 * 3452809 * 2
def baseEnd_3452809 : Nat := 1772950625170086602608327

theorem tailTrace_3452809 : CollatzResearch.WordTrace tailWord_3452809 prefixEnd_3452809 1772950625170086602608327 := by
  unfold tailWord_3452809
  simp only [CollatzResearch.WordTrace]
  refine ⟨125934290148070160674465481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83956193432046773782976987 125934290148070160674465481)
  ·
    refine ⟨94450717611052620505849111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125934290148070160674465481 94450717611052620505849111)
    ·
      refine ⟨141676076416578930758773667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94450717611052620505849111 141676076416578930758773667)
      ·
        refine ⟨212514114624868396138160501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141676076416578930758773667 212514114624868396138160501)
        ·
          refine ⟨19923198246081412137952547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 212514114624868396138160501 19923198246081412137952547)
          ·
            refine ⟨29884797369122118206928821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19923198246081412137952547 29884797369122118206928821)
            ·
              refine ⟨2801699753355198581899577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29884797369122118206928821 2801699753355198581899577)
              ·
                refine ⟨2101274815016398936424683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2801699753355198581899577 2101274815016398936424683)
                ·
                  refine ⟨3151912222524598404637025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2101274815016398936424683 3151912222524598404637025)
                  ·
                    refine ⟨2363934166893448803477769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3151912222524598404637025 2363934166893448803477769)
                    ·
                      refine ⟨1772950625170086602608327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2363934166893448803477769 1772950625170086602608327)
                      ·
                        rfl

theorem cell23_3452809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 2, 1, 2, 2].length) (baseStart_3452809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452809 prefixEnd_3452809 := by exact prefixLift 3452809
  have htrace : WordTrace (prefixWord ++ tailWord_3452809) baseStart_3452809 baseEnd_3452809 := by
    simpa [prefixWord, tailWord_3452809, baseEnd_3452809] using wordTrace_append hprefix tailTrace_3452809
  have hstable : (prefixWord ++ tailWord_3452809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452809).length < 2 ^ (prefixWord ++ tailWord_3452809).sum := by decide
  have hdescent : baseEnd_3452809 < baseStart_3452809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452846 : List Nat := [4, 1, 5, 1, 2, 1, 1, 1, 1, 1, 5]
def baseStart_3452846 : Nat := 118140960795 + 3452846 * 2 ^ 59
def prefixEnd_3452846 : Nat := 4983230072969 + 3 ^ 40 * 3452846 * 2
def baseEnd_3452846 : Nat := 1772969623954302957845657

theorem tailTrace_3452846 : CollatzResearch.WordTrace tailWord_3452846 prefixEnd_3452846 1772969623954302957845657 := by
  unfold tailWord_3452846
  simp only [CollatzResearch.WordTrace]
  refine ⟨15741954956117014499195299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83957093099290743995708261 15741954956117014499195299)
  ·
    refine ⟨23612932434175521748792949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15741954956117014499195299 23612932434175521748792949)
    ·
      refine ⟨2213712415703955163949339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23612932434175521748792949 2213712415703955163949339)
      ·
        refine ⟨3320568623555932745924009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2213712415703955163949339 3320568623555932745924009)
        ·
          refine ⟨2490426467666949559443007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3320568623555932745924009 2490426467666949559443007)
          ·
            refine ⟨3735639701500424339164511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2490426467666949559443007 3735639701500424339164511)
            ·
              refine ⟨5603459552250636508746767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3735639701500424339164511 5603459552250636508746767)
              ·
                refine ⟨8405189328375954763120151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5603459552250636508746767 8405189328375954763120151)
                ·
                  refine ⟨12607783992563932144680227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8405189328375954763120151 12607783992563932144680227)
                  ·
                    refine ⟨18911675988845898217020341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12607783992563932144680227 18911675988845898217020341)
                    ·
                      refine ⟨1772969623954302957845657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18911675988845898217020341 1772969623954302957845657)
                      ·
                        rfl

theorem cell23_3452846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_3452846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452846 prefixEnd_3452846 := by exact prefixLift 3452846
  have htrace : WordTrace (prefixWord ++ tailWord_3452846) baseStart_3452846 baseEnd_3452846 := by
    simpa [prefixWord, tailWord_3452846, baseEnd_3452846] using wordTrace_append hprefix tailTrace_3452846
  have hstable : (prefixWord ++ tailWord_3452846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452846).length < 2 ^ (prefixWord ++ tailWord_3452846).sum := by decide
  have hdescent : baseEnd_3452846 < baseStart_3452846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452851 : List Nat := [1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 5]
def baseStart_3452851 : Nat := 118140960795 + 3452851 * 2 ^ 59
def prefixEnd_3452851 : Nat := 4983230072969 + 3 ^ 40 * 3452851 * 2
def baseEnd_3452851 : Nat := 1772972191357575438283133

theorem tailTrace_3452851 : CollatzResearch.WordTrace tailWord_3452851 prefixEnd_3452851 1772972191357575438283133 := by
  unfold tailWord_3452851
  simp only [CollatzResearch.WordTrace]
  refine ⟨125935822013918001847494407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83957214675945334564996271 125935822013918001847494407)
  ·
    refine ⟨188903733020877002771241611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125935822013918001847494407 188903733020877002771241611)
    ·
      refine ⟨283355599531315504156862417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188903733020877002771241611 283355599531315504156862417)
      ·
        refine ⟨212516699648486628117646813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283355599531315504156862417 212516699648486628117646813)
        ·
          refine ⟨79693762368182485544117555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212516699648486628117646813 79693762368182485544117555)
          ·
            refine ⟨119540643552273728316176333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79693762368182485544117555 119540643552273728316176333)
            ·
              refine ⟨44827741332102648118566125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119540643552273728316176333 44827741332102648118566125)
              ·
                refine ⟨16810402999538493044462297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44827741332102648118566125 16810402999538493044462297)
                ·
                  refine ⟨12607802249653869783346723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16810402999538493044462297 12607802249653869783346723)
                  ·
                    refine ⟨18911703374480804675020085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12607802249653869783346723 18911703374480804675020085)
                    ·
                      refine ⟨1772972191357575438283133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18911703374480804675020085 1772972191357575438283133)
                      ·
                        rfl

theorem cell23_3452851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 5].length) (baseStart_3452851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452851 prefixEnd_3452851 := by exact prefixLift 3452851
  have htrace : WordTrace (prefixWord ++ tailWord_3452851) baseStart_3452851 baseEnd_3452851 := by
    simpa [prefixWord, tailWord_3452851, baseEnd_3452851] using wordTrace_append hprefix tailTrace_3452851
  have hstable : (prefixWord ++ tailWord_3452851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452851).length < 2 ^ (prefixWord ++ tailWord_3452851).sum := by decide
  have hdescent : baseEnd_3452851 < baseStart_3452851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452860 : List Nat := [2, 2, 2, 5, 2, 1, 2, 2, 1, 2, 2]
def baseStart_3452860 : Nat := 118140960795 + 3452860 * 2 ^ 59
def prefixEnd_3452860 : Nat := 4983230072969 + 3 ^ 40 * 3452860 * 2
def baseEnd_3452860 : Nat := 1772976812683465903070593

theorem tailTrace_3452860 : CollatzResearch.WordTrace tailWord_3452860 prefixEnd_3452860 1772976812683465903070593 := by
  unfold tailWord_3452860
  simp only [CollatzResearch.WordTrace]
  refine ⟨62968075135442698192286017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83957433513923597589714689 62968075135442698192286017)
  ·
    refine ⟨47226056351582023644214513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62968075135442698192286017 47226056351582023644214513)
    ·
      refine ⟨35419542263686517733160885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47226056351582023644214513 35419542263686517733160885)
      ·
        refine ⟨3320582087220611037483833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35419542263686517733160885 3320582087220611037483833)
        ·
          refine ⟨2490436565415458278112875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3320582087220611037483833 2490436565415458278112875)
          ·
            refine ⟨3735654848123187417169313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2490436565415458278112875 3735654848123187417169313)
            ·
              refine ⟨2801741136092390562876985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3735654848123187417169313 2801741136092390562876985)
              ·
                refine ⟨2101305852069292922157739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2801741136092390562876985 2101305852069292922157739)
                ·
                  refine ⟨3151958778103939383236609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2101305852069292922157739 3151958778103939383236609)
                  ·
                    refine ⟨2363969083577954537427457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3151958778103939383236609 2363969083577954537427457)
                    ·
                      refine ⟨1772976812683465903070593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2363969083577954537427457 1772976812683465903070593)
                      ·
                        rfl

theorem cell23_3452860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_3452860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452860 prefixEnd_3452860 := by exact prefixLift 3452860
  have htrace : WordTrace (prefixWord ++ tailWord_3452860) baseStart_3452860 baseEnd_3452860 := by
    simpa [prefixWord, tailWord_3452860, baseEnd_3452860] using wordTrace_append hprefix tailTrace_3452860
  have hstable : (prefixWord ++ tailWord_3452860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452860).length < 2 ^ (prefixWord ++ tailWord_3452860).sum := by decide
  have hdescent : baseEnd_3452860 < baseStart_3452860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452871 : List Nat := [1, 1, 4, 1, 1, 2, 1, 5, 7]
def baseStart_3452871 : Nat := 118140960795 + 3452871 * 2 ^ 59
def prefixEnd_3452871 : Nat := 4983230072969 + 3 ^ 40 * 3452871 * 2
def baseEnd_3452871 : Nat := 196998051218962817781449

theorem tailTrace_3452871 : CollatzResearch.WordTrace tailWord_3452871 prefixEnd_3452871 196998051218962817781449 := by
  unfold tailWord_3452871
  simp only [CollatzResearch.WordTrace]
  refine ⟨125936551473845545263222467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83957700982563696842148311 125936551473845545263222467)
  ·
    refine ⟨188904827210768317894833701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125936551473845545263222467 188904827210768317894833701)
    ·
      refine ⟨35419655102019059605281319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188904827210768317894833701 35419655102019059605281319)
      ·
        refine ⟨53129482653028589407921979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35419655102019059605281319 53129482653028589407921979)
        ·
          refine ⟨79694223979542884111882969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53129482653028589407921979 79694223979542884111882969)
          ·
            refine ⟨59770667984657163083912227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79694223979542884111882969 59770667984657163083912227)
            ·
              refine ⟨89656001976985744625868341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59770667984657163083912227 89656001976985744625868341)
              ·
                refine ⟨8405250185342413558675157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89656001976985744625868341 8405250185342413558675157)
                ·
                  refine ⟨196998051218962817781449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8405250185342413558675157 196998051218962817781449)
                  ·
                    rfl

theorem cell23_3452871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 7].length) (baseStart_3452871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452871 prefixEnd_3452871 := by exact prefixLift 3452871
  have htrace : WordTrace (prefixWord ++ tailWord_3452871) baseStart_3452871 baseEnd_3452871 := by
    simpa [prefixWord, tailWord_3452871, baseEnd_3452871] using wordTrace_append hprefix tailTrace_3452871
  have hstable : (prefixWord ++ tailWord_3452871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452871).length < 2 ^ (prefixWord ++ tailWord_3452871).sum := by decide
  have hdescent : baseEnd_3452871 < baseStart_3452871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452878 : List Nat := [4, 1, 1, 1, 2, 2, 3, 1, 2, 2, 4]
def baseStart_3452878 : Nat := 118140960795 + 3452878 * 2 ^ 59
def prefixEnd_3452878 : Nat := 4983230072969 + 3 ^ 40 * 3452878 * 2
def baseEnd_3452878 : Nat := 1772986055335246832645509

theorem tailTrace_3452878 : CollatzResearch.WordTrace tailWord_3452878 prefixEnd_3452878 1772986055335246832645509 := by
  unfold tailWord_3452878
  simp only [CollatzResearch.WordTrace]
  refine ⟨15742100848102523182340911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83957871189880123639151525 15742100848102523182340911)
  ·
    refine ⟨23613151272153784773511367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15742100848102523182340911 23613151272153784773511367)
    ·
      refine ⟨35419726908230677160267051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23613151272153784773511367 35419726908230677160267051)
      ·
        refine ⟨53129590362346015740400577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35419726908230677160267051 53129590362346015740400577)
        ·
          refine ⟨39847192771759511805300433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53129590362346015740400577 39847192771759511805300433)
          ·
            refine ⟨29885394578819633853975325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39847192771759511805300433 29885394578819633853975325)
            ·
              refine ⟨11207022967057362695240747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29885394578819633853975325 11207022967057362695240747)
              ·
                refine ⟨16810534450586044042861121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11207022967057362695240747 16810534450586044042861121)
                ·
                  refine ⟨12607900837939533032145841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16810534450586044042861121 12607900837939533032145841)
                  ·
                    refine ⟨9455925628454649774109381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12607900837939533032145841 9455925628454649774109381)
                    ·
                      refine ⟨1772986055335246832645509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9455925628454649774109381 1772986055335246832645509)
                      ·
                        rfl

theorem cell23_3452878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_3452878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452878 prefixEnd_3452878 := by exact prefixLift 3452878
  have htrace : WordTrace (prefixWord ++ tailWord_3452878) baseStart_3452878 baseEnd_3452878 := by
    simpa [prefixWord, tailWord_3452878, baseEnd_3452878] using wordTrace_append hprefix tailTrace_3452878
  have hstable : (prefixWord ++ tailWord_3452878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452878).length < 2 ^ (prefixWord ++ tailWord_3452878).sum := by decide
  have hdescent : baseEnd_3452878 < baseStart_3452878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3452978 : List Nat := [3, 2, 1, 1, 2, 3, 2, 1, 8]
def baseStart_3452978 : Nat := 118140960795 + 3452978 * 2 ^ 59
def prefixEnd_3452978 : Nat := 4983230072969 + 3 ^ 40 * 3452978 * 2
def baseEnd_3452978 : Nat := 197004155933410715710561

theorem tailTrace_3452978 : CollatzResearch.WordTrace tailWord_3452978 prefixEnd_3452978 197004155933410715710561 := by
  unfold tailWord_3452978
  simp only [CollatzResearch.WordTrace]
  refine ⟨31485113521114475634341897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83960302722971935024911725 31485113521114475634341897)
  ·
    refine ⟨23613835140835856725756423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31485113521114475634341897 23613835140835856725756423)
    ·
      refine ⟨35420752711253785088634635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23613835140835856725756423 35420752711253785088634635)
      ·
        refine ⟨53131129066880677632951953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35420752711253785088634635 53131129066880677632951953)
        ·
          refine ⟨39848346800160508224713965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53131129066880677632951953 39848346800160508224713965)
          ·
            refine ⟨14943130050060190584267737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39848346800160508224713965 14943130050060190584267737)
            ·
              refine ⟨11207347537545142938200803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14943130050060190584267737 11207347537545142938200803)
              ·
                refine ⟨16811021306317714407301205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11207347537545142938200803 16811021306317714407301205)
                ·
                  refine ⟨197004155933410715710561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16811021306317714407301205 197004155933410715710561)
                  ·
                    rfl

theorem cell23_3452978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 8].length) (baseStart_3452978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3452978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3452978 prefixEnd_3452978 := by exact prefixLift 3452978
  have htrace : WordTrace (prefixWord ++ tailWord_3452978) baseStart_3452978 baseEnd_3452978 := by
    simpa [prefixWord, tailWord_3452978, baseEnd_3452978] using wordTrace_append hprefix tailTrace_3452978
  have hstable : (prefixWord ++ tailWord_3452978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3452978).length < 2 ^ (prefixWord ++ tailWord_3452978).sum := by decide
  have hdescent : baseEnd_3452978 < baseStart_3452978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3452978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453015 : List Nat := [1, 1, 3, 2, 2, 1, 2, 3, 1, 5, 2]
def baseStart_3453015 : Nat := 118140960795 + 3453015 * 2 ^ 59
def prefixEnd_3453015 : Nat := 4983230072969 + 3 ^ 40 * 3453015 * 2
def baseEnd_3453015 : Nat := 1773056402184912796632379

theorem tailTrace_3453015 : CollatzResearch.WordTrace tailWord_3453015 prefixEnd_3453015 1773056402184912796632379 := by
  unfold tailWord_3453015
  simp only [CollatzResearch.WordTrace]
  refine ⟨125941803585323857856464499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83961202390215905237642999 125941803585323857856464499)
  ·
    refine ⟨188912705377985786784696749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125941803585323857856464499 188912705377985786784696749)
    ·
      refine ⟨70842264516744670044261281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188912705377985786784696749 70842264516744670044261281)
      ·
        refine ⟨53131698387558502533195961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70842264516744670044261281 53131698387558502533195961)
        ·
          refine ⟨39848773790668876899896971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53131698387558502533195961 39848773790668876899896971)
          ·
            refine ⟨59773160686003315349845457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39848773790668876899896971 59773160686003315349845457)
            ·
              refine ⟨44829870514502486512384093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59773160686003315349845457 44829870514502486512384093)
              ·
                refine ⟨16811201442938432442144035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44829870514502486512384093 16811201442938432442144035)
                ·
                  refine ⟨25216802164407648663216053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16811201442938432442144035 25216802164407648663216053)
                  ·
                    refine ⟨2364075202913217062176505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25216802164407648663216053 2364075202913217062176505)
                    ·
                      refine ⟨1773056402184912796632379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2364075202913217062176505 1773056402184912796632379)
                      ·
                        rfl

theorem cell23_3453015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 5, 2].length) (baseStart_3453015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3453015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3453015 prefixEnd_3453015 := by exact prefixLift 3453015
  have htrace : WordTrace (prefixWord ++ tailWord_3453015) baseStart_3453015 baseEnd_3453015 := by
    simpa [prefixWord, tailWord_3453015, baseEnd_3453015] using wordTrace_append hprefix tailTrace_3453015
  have hstable : (prefixWord ++ tailWord_3453015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453015).length < 2 ^ (prefixWord ++ tailWord_3453015).sum := by decide
  have hdescent : baseEnd_3453015 < baseStart_3453015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453039 : List Nat := [1, 1, 2, 1, 3, 5, 1, 4, 1, 1, 3]
def baseStart_3453039 : Nat := 118140960795 + 3453039 * 2 ^ 59
def prefixEnd_3453039 : Nat := 4983230072969 + 3 ^ 40 * 3453039 * 2
def baseEnd_3453039 : Nat := 1773068725720620702732269

theorem tailTrace_3453039 : CollatzResearch.WordTrace tailWord_3453039 prefixEnd_3453039 1773068725720620702732269 := by
  unfold tailWord_3453039
  simp only [CollatzResearch.WordTrace]
  refine ⟨125942678937236909955338171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83961785958157939970225447 125942678937236909955338171)
  ·
    refine ⟨188914018405855364933007257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125942678937236909955338171 188914018405855364933007257)
    ·
      refine ⟨141685513804391523699755443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188914018405855364933007257 141685513804391523699755443)
      ·
        refine ⟨212528270706587285549633165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141685513804391523699755443 212528270706587285549633165)
        ·
          refine ⟨79698101514970232081112437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212528270706587285549633165 79698101514970232081112437)
          ·
            refine ⟨7471697017028459257604291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79698101514970232081112437 7471697017028459257604291)
            ·
              refine ⟨11207545525542688886406437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7471697017028459257604291 11207545525542688886406437)
              ·
                refine ⟨2101414786039254166201207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11207545525542688886406437 2101414786039254166201207)
                ·
                  refine ⟨3152122179058881249301811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2101414786039254166201207 3152122179058881249301811)
                  ·
                    refine ⟨4728183268588321873952717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3152122179058881249301811 4728183268588321873952717)
                    ·
                      refine ⟨1773068725720620702732269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4728183268588321873952717 1773068725720620702732269)
                      ·
                        rfl

theorem cell23_3453039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 4, 1, 1, 3].length) (baseStart_3453039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3453039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3453039 prefixEnd_3453039 := by exact prefixLift 3453039
  have htrace : WordTrace (prefixWord ++ tailWord_3453039) baseStart_3453039 baseEnd_3453039 := by
    simpa [prefixWord, tailWord_3453039, baseEnd_3453039] using wordTrace_append hprefix tailTrace_3453039
  have hstable : (prefixWord ++ tailWord_3453039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453039).length < 2 ^ (prefixWord ++ tailWord_3453039).sum := by decide
  have hdescent : baseEnd_3453039 < baseStart_3453039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453048 : List Nat := [2, 1, 2, 1, 1, 1, 3, 3, 3, 1, 5]
def baseStart_3453048 : Nat := 118140960795 + 3453048 * 2 ^ 59
def prefixEnd_3453048 : Nat := 4983230072969 + 3 ^ 40 * 3453048 * 2
def baseEnd_3453048 : Nat := 1773073347046511167519727

theorem tailTrace_3453048 : CollatzResearch.WordTrace tailWord_3453048 prefixEnd_3453048 1773073347046511167519727 := by
  unfold tailWord_3453048
  simp only [CollatzResearch.WordTrace]
  refine ⟨62971503597102152246207899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83962004796136202994943865 62971503597102152246207899)
  ·
    refine ⟨94457255395653228369311849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62971503597102152246207899 94457255395653228369311849)
    ·
      refine ⟨70842941546739921276983887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94457255395653228369311849 70842941546739921276983887)
      ·
        refine ⟨106264412320109881915475831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70842941546739921276983887 106264412320109881915475831)
        ·
          refine ⟨159396618480164822873213747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106264412320109881915475831 159396618480164822873213747)
          ·
            refine ⟨239094927720247234309820621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159396618480164822873213747 239094927720247234309820621)
            ·
              refine ⟨89660597895092712866182733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 239094927720247234309820621 89660597895092712866182733)
              ·
                refine ⟨33622724210659767324818525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89660597895092712866182733 33622724210659767324818525)
                ·
                  refine ⟨12608521578997412746806947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33622724210659767324818525 12608521578997412746806947)
                  ·
                    refine ⟨18912782368496119120210421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12608521578997412746806947 18912782368496119120210421)
                    ·
                      refine ⟨1773073347046511167519727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18912782368496119120210421 1773073347046511167519727)
                      ·
                        rfl

theorem cell23_3453048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 3, 1, 5].length) (baseStart_3453048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3453048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3453048 prefixEnd_3453048 := by exact prefixLift 3453048
  have htrace : WordTrace (prefixWord ++ tailWord_3453048) baseStart_3453048 baseEnd_3453048 := by
    simpa [prefixWord, tailWord_3453048, baseEnd_3453048] using wordTrace_append hprefix tailTrace_3453048
  have hstable : (prefixWord ++ tailWord_3453048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453048).length < 2 ^ (prefixWord ++ tailWord_3453048).sum := by decide
  have hdescent : baseEnd_3453048 < baseStart_3453048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453065 : List Nat := [1, 2, 1, 1, 4, 2, 1, 3, 3, 2, 3]
def baseStart_3453065 : Nat := 118140960795 + 3453065 * 2 ^ 59
def prefixEnd_3453065 : Nat := 4983230072969 + 3 ^ 40 * 3453065 * 2
def baseEnd_3453065 : Nat := 1773082076217637601007149

theorem tailTrace_3453065 : CollatzResearch.WordTrace tailWord_3453065 prefixEnd_3453065 1773082076217637601007149 := by
  unfold tailWord_3453065
  simp only [CollatzResearch.WordTrace]
  refine ⟨125943627235142716395784649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83962418156761810930523099 125943627235142716395784649)
  ·
    refine ⟨94457720426357037296838487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125943627235142716395784649 94457720426357037296838487)
    ·
      refine ⟨141686580639535555945257731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94457720426357037296838487 141686580639535555945257731)
      ·
        refine ⟨212529870959303333917886597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141686580639535555945257731 212529870959303333917886597)
        ·
          refine ⟨39849350804869375109603737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212529870959303333917886597 39849350804869375109603737)
          ·
            refine ⟨29887013103652031332202803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39849350804869375109603737 29887013103652031332202803)
            ·
              refine ⟨44830519655478046998304205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29887013103652031332202803 44830519655478046998304205)
              ·
                refine ⟨16811444870804267624364077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44830519655478046998304205 16811444870804267624364077)
                ·
                  refine ⟨6304291826551600359136529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16811444870804267624364077 6304291826551600359136529)
                  ·
                    refine ⟨4728218869913700269352397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6304291826551600359136529 4728218869913700269352397)
                    ·
                      refine ⟨1773082076217637601007149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4728218869913700269352397 1773082076217637601007149)
                      ·
                        rfl

theorem cell23_3453065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 3, 2, 3].length) (baseStart_3453065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3453065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3453065 prefixEnd_3453065 := by exact prefixLift 3453065
  have htrace : WordTrace (prefixWord ++ tailWord_3453065) baseStart_3453065 baseEnd_3453065 := by
    simpa [prefixWord, tailWord_3453065, baseEnd_3453065] using wordTrace_append hprefix tailTrace_3453065
  have hstable : (prefixWord ++ tailWord_3453065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453065).length < 2 ^ (prefixWord ++ tailWord_3453065).sum := by decide
  have hdescent : baseEnd_3453065 < baseStart_3453065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453089 : List Nat := [1, 2, 3, 3, 1, 4, 1, 2, 2, 4]
def baseStart_3453089 : Nat := 118140960795 + 3453089 * 2 ^ 59
def prefixEnd_3453089 : Nat := 4983230072969 + 3 ^ 40 * 3453089 * 2
def baseEnd_3453089 : Nat := 591031466584448502369013

theorem tailTrace_3453089 : CollatzResearch.WordTrace tailWord_3453089 prefixEnd_3453089 591031466584448502369013 := by
  unfold tailWord_3453089
  simp only [CollatzResearch.WordTrace]
  refine ⟨125944502587055768494658321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83963001724703845663105547 125944502587055768494658321)
  ·
    refine ⟨94458376940291826370993741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125944502587055768494658321 94458376940291826370993741)
    ·
      refine ⟨35421891352609434889122653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94458376940291826370993741 35421891352609434889122653)
      ·
        refine ⟨13283209257228538083420995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35421891352609434889122653 13283209257228538083420995)
        ·
          refine ⟨19924813885842807125131493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13283209257228538083420995 19924813885842807125131493)
          ·
            refine ⟨3735902603595526335962155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19924813885842807125131493 3735902603595526335962155)
            ·
              refine ⟨5603853905393289503943233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3735902603595526335962155 5603853905393289503943233)
              ·
                refine ⟨4202890429044967127957425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5603853905393289503943233 4202890429044967127957425)
                ·
                  refine ⟨3152167821783725345968069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4202890429044967127957425 3152167821783725345968069)
                  ·
                    refine ⟨591031466584448502369013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3152167821783725345968069 591031466584448502369013)
                    ·
                      rfl

theorem cell23_3453089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 2, 2, 4].length) (baseStart_3453089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3453089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3453089 prefixEnd_3453089 := by exact prefixLift 3453089
  have htrace : WordTrace (prefixWord ++ tailWord_3453089) baseStart_3453089 baseEnd_3453089 := by
    simpa [prefixWord, tailWord_3453089, baseEnd_3453089] using wordTrace_append hprefix tailTrace_3453089
  have hstable : (prefixWord ++ tailWord_3453089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453089).length < 2 ^ (prefixWord ++ tailWord_3453089).sum := by decide
  have hdescent : baseEnd_3453089 < baseStart_3453089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453186 : List Nat := [3, 4, 1, 1, 2, 2, 1, 2, 1, 4, 2]
def baseStart_3453186 : Nat := 118140960795 + 3453186 * 2 ^ 59
def prefixEnd_3453186 : Nat := 4983230072969 + 3 ^ 40 * 3453186 * 2
def baseEnd_3453186 : Nat := 1773144207376831627594093

theorem tailTrace_3453186 : CollatzResearch.WordTrace tailWord_3453186 prefixEnd_3453186 1773144207376831627594093 := by
  unfold tailWord_3453186
  simp only [CollatzResearch.WordTrace]
  refine ⟨31487010116926088515234853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83965360311802902707292941 31487010116926088515234853)
  ·
    refine ⟨5903814396923641596606535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31487010116926088515234853 5903814396923641596606535)
    ·
      refine ⟨8855721595385462394909803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5903814396923641596606535 8855721595385462394909803)
      ·
        refine ⟨13283582393078193592364705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8855721595385462394909803 13283582393078193592364705)
        ·
          refine ⟨9962686794808645194273529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13283582393078193592364705 9962686794808645194273529)
          ·
            refine ⟨7472015096106483895705147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9962686794808645194273529 7472015096106483895705147)
            ·
              refine ⟨11208022644159725843557721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7472015096106483895705147 11208022644159725843557721)
              ·
                refine ⟨8406016983119794382668291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11208022644159725843557721 8406016983119794382668291)
                ·
                  refine ⟨12609025474679691574002437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8406016983119794382668291 12609025474679691574002437)
                  ·
                    refine ⟨2364192276502442170125457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12609025474679691574002437 2364192276502442170125457)
                    ·
                      refine ⟨1773144207376831627594093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2364192276502442170125457 1773144207376831627594093)
                      ·
                        rfl

theorem cell23_3453186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_3453186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3453186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3453186 prefixEnd_3453186 := by exact prefixLift 3453186
  have htrace : WordTrace (prefixWord ++ tailWord_3453186) baseStart_3453186 baseEnd_3453186 := by
    simpa [prefixWord, tailWord_3453186, baseEnd_3453186] using wordTrace_append hprefix tailTrace_3453186
  have hstable : (prefixWord ++ tailWord_3453186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453186).length < 2 ^ (prefixWord ++ tailWord_3453186).sum := by decide
  have hdescent : baseEnd_3453186 < baseStart_3453186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453242 : List Nat := [3, 1, 1, 1, 4, 3, 1, 1, 1, 3, 4]
def baseStart_3453242 : Nat := 118140960795 + 3453242 * 2 ^ 59
def prefixEnd_3453242 : Nat := 4983230072969 + 3 ^ 40 * 3453242 * 2
def baseEnd_3453242 : Nat := 1773172962293483408493835

theorem tailTrace_3453242 : CollatzResearch.WordTrace tailWord_3453242 prefixEnd_3453242 1773172962293483408493835 := by
  unfold tailWord_3453242
  simp only [CollatzResearch.WordTrace]
  refine ⟨31487520738875368906244495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83966721970334317083318653 31487520738875368906244495)
  ·
    refine ⟨47231281108313053359366743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31487520738875368906244495 47231281108313053359366743)
    ·
      refine ⟨70846921662469580039050115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47231281108313053359366743 70846921662469580039050115)
      ·
        refine ⟨106270382493704370058575173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70846921662469580039050115 106270382493704370058575173)
        ·
          refine ⟨19925696717569569385982845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106270382493704370058575173 19925696717569569385982845)
          ·
            refine ⟨7472136269088588519743567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19925696717569569385982845 7472136269088588519743567)
            ·
              refine ⟨11208204403632882779615351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7472136269088588519743567 11208204403632882779615351)
              ·
                refine ⟨16812306605449324169423027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11208204403632882779615351 16812306605449324169423027)
                ·
                  refine ⟨25218459908173986254134541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16812306605449324169423027 25218459908173986254134541)
                  ·
                    refine ⟨9456922465565244845300453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25218459908173986254134541 9456922465565244845300453)
                    ·
                      refine ⟨1773172962293483408493835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9456922465565244845300453 1773172962293483408493835)
                      ·
                        rfl

theorem cell23_3453242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 1, 3, 4].length) (baseStart_3453242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3453242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3453242 prefixEnd_3453242 := by exact prefixLift 3453242
  have htrace : WordTrace (prefixWord ++ tailWord_3453242) baseStart_3453242 baseEnd_3453242 := by
    simpa [prefixWord, tailWord_3453242, baseEnd_3453242] using wordTrace_append hprefix tailTrace_3453242
  have hstable : (prefixWord ++ tailWord_3453242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453242).length < 2 ^ (prefixWord ++ tailWord_3453242).sum := by decide
  have hdescent : baseEnd_3453242 < baseStart_3453242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453255 : List Nat := [1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 6]
def baseStart_3453255 : Nat := 118140960795 + 3453255 * 2 ^ 59
def prefixEnd_3453255 : Nat := 4983230072969 + 3 ^ 40 * 3453255 * 2
def baseEnd_3453255 : Nat := 1773179637541991857631275

theorem tailTrace_3453255 : CollatzResearch.WordTrace tailWord_3453255 prefixEnd_3453255 1773179637541991857631275 := by
  unfold tailWord_3453255
  simp only [CollatzResearch.WordTrace]
  refine ⟨125950557104454378845201219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83967038069636252563467479 125950557104454378845201219)
  ·
    refine ⟨188925835656681568267801829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125950557104454378845201219 188925835656681568267801829)
    ·
      refine ⟨35423594185627794050212843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188925835656681568267801829 35423594185627794050212843)
      ·
        refine ⟨53135391278441691075319265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35423594185627794050212843 53135391278441691075319265)
        ·
          refine ⟨39851543458831268306489449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53135391278441691075319265 39851543458831268306489449)
          ·
            refine ⟨29888657594123451229867087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39851543458831268306489449 29888657594123451229867087)
            ·
              refine ⟨44832986391185176844800631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29888657594123451229867087 44832986391185176844800631)
              ·
                refine ⟨67249479586777765267200947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44832986391185176844800631 67249479586777765267200947)
                ·
                  refine ⟨100874219380166647900801421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67249479586777765267200947 100874219380166647900801421)
                  ·
                    refine ⟨37827832267562492962800533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 100874219380166647900801421 37827832267562492962800533)
                    ·
                      refine ⟨1773179637541991857631275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37827832267562492962800533 1773179637541991857631275)
                      ·
                        rfl

theorem cell23_3453255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_3453255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3453255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3453255 prefixEnd_3453255 := by exact prefixLift 3453255
  have htrace : WordTrace (prefixWord ++ tailWord_3453255) baseStart_3453255 baseEnd_3453255 := by
    simpa [prefixWord, tailWord_3453255, baseEnd_3453255] using wordTrace_append hprefix tailTrace_3453255
  have hstable : (prefixWord ++ tailWord_3453255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453255).length < 2 ^ (prefixWord ++ tailWord_3453255).sum := by decide
  have hdescent : baseEnd_3453255 < baseStart_3453255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453369 : List Nat := [1, 2, 1, 4, 3, 1, 3, 1, 1, 1, 5]
def baseStart_3453369 : Nat := 118140960795 + 3453369 * 2 ^ 59
def prefixEnd_3453369 : Nat := 4983230072969 + 3 ^ 40 * 3453369 * 2
def baseEnd_3453369 : Nat := 1773238174336604411605751

theorem tailTrace_3453369 : CollatzResearch.WordTrace tailWord_3453369 prefixEnd_3453369 1773238174336604411605751 := by
  unfold tailWord_3453369
  simp only [CollatzResearch.WordTrace]
  refine ⟨125954715026041376314851161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83969810017360917543234107 125954715026041376314851161)
  ·
    refine ⟨94466036269531032236138371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125954715026041376314851161 94466036269531032236138371)
    ·
      refine ⟨141699054404296548354207557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94466036269531032236138371 141699054404296548354207557)
      ·
        refine ⟨26568572700805602816413917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141699054404296548354207557 26568572700805602816413917)
        ·
          refine ⟨9963214762802101056155219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26568572700805602816413917 9963214762802101056155219)
          ·
            refine ⟨14944822144203151584232829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9963214762802101056155219 14944822144203151584232829)
            ·
              refine ⟨5604308304076181844087311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14944822144203151584232829 5604308304076181844087311)
              ·
                refine ⟨8406462456114272766130967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5604308304076181844087311 8406462456114272766130967)
                ·
                  refine ⟨12609693684171409149196451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8406462456114272766130967 12609693684171409149196451)
                  ·
                    refine ⟨18914540526257113723794677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12609693684171409149196451 18914540526257113723794677)
                    ·
                      refine ⟨1773238174336604411605751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18914540526257113723794677 1773238174336604411605751)
                      ·
                        rfl

theorem cell23_3453369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_3453369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3453369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3453369 prefixEnd_3453369 := by exact prefixLift 3453369
  have htrace : WordTrace (prefixWord ++ tailWord_3453369) baseStart_3453369 baseEnd_3453369 := by
    simpa [prefixWord, tailWord_3453369, baseEnd_3453369] using wordTrace_append hprefix tailTrace_3453369
  have hstable : (prefixWord ++ tailWord_3453369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453369).length < 2 ^ (prefixWord ++ tailWord_3453369).sum := by decide
  have hdescent : baseEnd_3453369 < baseStart_3453369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453372 : List Nat := [2, 2, 2, 4, 1, 12]
def baseStart_3453372 : Nat := 118140960795 + 3453372 * 2 ^ 59
def prefixEnd_3453372 : Nat := 4983230072969 + 3 ^ 40 * 3453372 * 2
def baseEnd_3453372 : Nat := 7297282776866534567359

theorem tailTrace_3453372 : CollatzResearch.WordTrace tailWord_3453372 prefixEnd_3453372 7297282776866534567359 := by
  unfold tailWord_3453372
  simp only [CollatzResearch.WordTrace]
  refine ⟨62977412222515253913605185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83969882963353671884806913 62977412222515253913605185)
  ·
    refine ⟨47233059166886440435203889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62977412222515253913605185 47233059166886440435203889)
    ·
      refine ⟨35424794375164830326402917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47233059166886440435203889 35424794375164830326402917)
      ·
        refine ⟨6642148945343405686200547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35424794375164830326402917 6642148945343405686200547)
        ·
          refine ⟨9963223418015108529300821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6642148945343405686200547 9963223418015108529300821)
          ·
            refine ⟨7297282776866534567359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 9963223418015108529300821 7297282776866534567359)
            ·
              rfl

theorem cell23_3453372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 12].length) (baseStart_3453372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3453372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3453372 prefixEnd_3453372 := by exact prefixLift 3453372
  have htrace : WordTrace (prefixWord ++ tailWord_3453372) baseStart_3453372 baseEnd_3453372 := by
    simpa [prefixWord, tailWord_3453372, baseEnd_3453372] using wordTrace_append hprefix tailTrace_3453372
  have hstable : (prefixWord ++ tailWord_3453372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453372).length < 2 ^ (prefixWord ++ tailWord_3453372).sum := by decide
  have hdescent : baseEnd_3453372 < baseStart_3453372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453396 : List Nat := [2, 4, 1, 2, 2, 2, 2, 1, 1, 2, 4]
def baseStart_3453396 : Nat := 118140960795 + 3453396 * 2 ^ 59
def prefixEnd_3453396 : Nat := 4983230072969 + 3 ^ 40 * 3453396 * 2
def baseEnd_3453396 : Nat := 1773252038314275805968127

theorem tailTrace_3453396 : CollatzResearch.WordTrace tailWord_3453396 prefixEnd_3453396 1773252038314275805968127 := by
  unfold tailWord_3453396
  simp only [CollatzResearch.WordTrace]
  refine ⟨62977849898471779963042021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83970466531295706617389361 62977849898471779963042021)
  ·
    refine ⟨11808346855963458743070379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62977849898471779963042021 11808346855963458743070379)
    ·
      refine ⟨17712520283945188114605569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11808346855963458743070379 17712520283945188114605569)
      ·
        refine ⟨13284390212958891085954177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17712520283945188114605569 13284390212958891085954177)
        ·
          refine ⟨9963292659719168314465633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13284390212958891085954177 9963292659719168314465633)
          ·
            refine ⟨7472469494789376235849225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9963292659719168314465633 7472469494789376235849225)
            ·
              refine ⟨5604352121092032176886919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7472469494789376235849225 5604352121092032176886919)
              ·
                refine ⟨8406528181638048265330379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5604352121092032176886919 8406528181638048265330379)
                ·
                  refine ⟨12609792272457072397995569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8406528181638048265330379 12609792272457072397995569)
                  ·
                    refine ⟨9457344204342804298496677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12609792272457072397995569 9457344204342804298496677)
                    ·
                      refine ⟨1773252038314275805968127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9457344204342804298496677 1773252038314275805968127)
                      ·
                        rfl

theorem cell23_3453396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_3453396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3453396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3453396 prefixEnd_3453396 := by exact prefixLift 3453396
  have htrace : WordTrace (prefixWord ++ tailWord_3453396) baseStart_3453396 baseEnd_3453396 := by
    simpa [prefixWord, tailWord_3453396, baseEnd_3453396] using wordTrace_append hprefix tailTrace_3453396
  have hstable : (prefixWord ++ tailWord_3453396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453396).length < 2 ^ (prefixWord ++ tailWord_3453396).sum := by decide
  have hdescent : baseEnd_3453396 < baseStart_3453396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453399 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 8, 1, 3]
def baseStart_3453399 : Nat := 118140960795 + 3453399 * 2 ^ 59
def prefixEnd_3453399 : Nat := 4983230072969 + 3 ^ 40 * 3453399 * 2
def baseEnd_3453399 : Nat := 1773253578756239294230613

theorem tailTrace_3453399 : CollatzResearch.WordTrace tailWord_3453399 prefixEnd_3453399 1773253578756239294230613 := by
  unfold tailWord_3453399
  simp only [CollatzResearch.WordTrace]
  refine ⟨125955809215932691438443251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83970539477288460958962167 125955809215932691438443251)
  ·
    refine ⟨188933713823899037157664877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125955809215932691438443251 188933713823899037157664877)
    ·
      refine ⟨70850142683962138934124329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188933713823899037157664877 70850142683962138934124329)
      ·
        refine ⟨53137607012971604200593247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70850142683962138934124329 53137607012971604200593247)
        ·
          refine ⟨79706410519457406300889871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53137607012971604200593247 79706410519457406300889871)
          ·
            refine ⟨119559615779186109451334807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79706410519457406300889871 119559615779186109451334807)
            ·
              refine ⟨179339423668779164177002211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119559615779186109451334807 179339423668779164177002211)
              ·
                refine ⟨269009135503168746265503317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179339423668779164177002211 269009135503168746265503317)
                ·
                  refine ⟨3152450806677758745298867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 269009135503168746265503317 3152450806677758745298867)
                  ·
                    refine ⟨4728676210016638117948301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3152450806677758745298867 4728676210016638117948301)
                    ·
                      refine ⟨1773253578756239294230613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4728676210016638117948301 1773253578756239294230613)
                      ·
                        rfl

theorem cell23_3453399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 8, 1, 3].length) (baseStart_3453399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3453399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3453399 prefixEnd_3453399 := by exact prefixLift 3453399
  have htrace : WordTrace (prefixWord ++ tailWord_3453399) baseStart_3453399 baseEnd_3453399 := by
    simpa [prefixWord, tailWord_3453399, baseEnd_3453399] using wordTrace_append hprefix tailTrace_3453399
  have hstable : (prefixWord ++ tailWord_3453399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453399).length < 2 ^ (prefixWord ++ tailWord_3453399).sum := by decide
  have hdescent : baseEnd_3453399 < baseStart_3453399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453402 : List Nat := [3, 1, 1, 2, 3, 1, 1, 2, 2, 7]
def baseStart_3453402 : Nat := 118140960795 + 3453402 * 2 ^ 59
def prefixEnd_3453402 : Nat := 4983230072969 + 3 ^ 40 * 3453402 * 2
def baseEnd_3453402 : Nat := 591085039732734260831033

theorem tailTrace_3453402 : CollatzResearch.WordTrace tailWord_3453402 prefixEnd_3453402 591085039732734260831033 := by
  unfold tailWord_3453402
  simp only [CollatzResearch.WordTrace]
  refine ⟨31488979658730455737700615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83970612423281215300534973 31488979658730455737700615)
  ·
    refine ⟨47233469488095683606550923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31488979658730455737700615 47233469488095683606550923)
    ·
      refine ⟨70850204232143525409826385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47233469488095683606550923 70850204232143525409826385)
      ·
        refine ⟨53137653174107644057369789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70850204232143525409826385 53137653174107644057369789)
        ·
          refine ⟨19926619940290366521513671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53137653174107644057369789 19926619940290366521513671)
          ·
            refine ⟨29889929910435549782270507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19926619940290366521513671 29889929910435549782270507)
            ·
              refine ⟨44834894865653324673405761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29889929910435549782270507 44834894865653324673405761)
              ·
                refine ⟨33626171149239993505054321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44834894865653324673405761 33626171149239993505054321)
                ·
                  refine ⟨25219628361929995128790741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33626171149239993505054321 25219628361929995128790741)
                  ·
                    refine ⟨591085039732734260831033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25219628361929995128790741 591085039732734260831033)
                    ·
                      rfl

theorem cell23_3453402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 2, 7].length) (baseStart_3453402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3453402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3453402 prefixEnd_3453402 := by exact prefixLift 3453402
  have htrace : WordTrace (prefixWord ++ tailWord_3453402) baseStart_3453402 baseEnd_3453402 := by
    simpa [prefixWord, tailWord_3453402, baseEnd_3453402] using wordTrace_append hprefix tailTrace_3453402
  have hstable : (prefixWord ++ tailWord_3453402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453402).length < 2 ^ (prefixWord ++ tailWord_3453402).sum := by decide
  have hdescent : baseEnd_3453402 < baseStart_3453402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453432 : List Nat := [2, 1, 2, 1, 1, 4, 1, 1, 4, 6]
def baseStart_3453432 : Nat := 118140960795 + 3453432 * 2 ^ 59
def prefixEnd_3453432 : Nat := 4983230072969 + 3 ^ 40 * 3453432 * 2
def baseEnd_3453432 : Nat := 591090174539279221705987

theorem tailTrace_3453432 : CollatzResearch.WordTrace tailWord_3453432 prefixEnd_3453432 591090174539279221705987 := by
  unfold tailWord_3453432
  simp only [CollatzResearch.WordTrace]
  refine ⟨62978506412406569037197275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83971341883208758716263033 62978506412406569037197275)
  ·
    refine ⟨94467759618609853555795913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62978506412406569037197275 94467759618609853555795913)
    ·
      refine ⟨70850819713957390166846935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94467759618609853555795913 70850819713957390166846935)
      ·
        refine ⟨106276229570936085250270403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70850819713957390166846935 106276229570936085250270403)
        ·
          refine ⟨159414344356404127875405605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106276229570936085250270403 159414344356404127875405605)
          ·
            refine ⟨29890189566825773976638551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159414344356404127875405605 29890189566825773976638551)
            ·
              refine ⟨44835284350238660964957827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29890189566825773976638551 44835284350238660964957827)
              ·
                refine ⟨67252926525357991447436741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44835284350238660964957827 67252926525357991447436741)
                ·
                  refine ⟨12609923723504623396394389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67252926525357991447436741 12609923723504623396394389)
                  ·
                    refine ⟨591090174539279221705987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12609923723504623396394389 591090174539279221705987)
                    ·
                      rfl

theorem cell23_3453432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 4, 6].length) (baseStart_3453432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3453432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3453432 prefixEnd_3453432 := by exact prefixLift 3453432
  have htrace : WordTrace (prefixWord ++ tailWord_3453432) baseStart_3453432 baseEnd_3453432 := by
    simpa [prefixWord, tailWord_3453432, baseEnd_3453432] using wordTrace_append hprefix tailTrace_3453432
  have hstable : (prefixWord ++ tailWord_3453432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453432).length < 2 ^ (prefixWord ++ tailWord_3453432).sum := by decide
  have hdescent : baseEnd_3453432 < baseStart_3453432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453460 : List Nat := [2, 4, 3, 1, 1, 1, 1, 4, 1, 3, 2]
def baseStart_3453460 : Nat := 118140960795 + 3453460 * 2 ^ 59
def prefixEnd_3453460 : Nat := 4983230072969 + 3 ^ 40 * 3453460 * 2
def baseEnd_3453460 : Nat := 1773284901076163555567833

theorem tailTrace_3453460 : CollatzResearch.WordTrace tailWord_3453460 prefixEnd_3453460 1773284901076163555567833 := by
  unfold tailWord_3453460
  simp only [CollatzResearch.WordTrace]
  refine ⟨62979017034355849428206917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83972022712474465904275889 62979017034355849428206917)
  ·
    refine ⟨11808565693941721767788797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62979017034355849428206917 11808565693941721767788797)
    ·
      refine ⟨4428212135228145662920799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11808565693941721767788797 4428212135228145662920799)
      ·
        refine ⟨6642318202842218494381199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4428212135228145662920799 6642318202842218494381199)
        ·
          refine ⟨9963477304263327741571799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6642318202842218494381199 9963477304263327741571799)
          ·
            refine ⟨14945215956394991612357699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9963477304263327741571799 14945215956394991612357699)
            ·
              refine ⟨22417823934592487418536549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14945215956394991612357699 22417823934592487418536549)
              ·
                refine ⟨4203341987736091390975603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22417823934592487418536549 4203341987736091390975603)
                ·
                  refine ⟨6305012981604137086463405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4203341987736091390975603 6305012981604137086463405)
                  ·
                    refine ⟨2364379868101551407423777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6305012981604137086463405 2364379868101551407423777)
                    ·
                      refine ⟨1773284901076163555567833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2364379868101551407423777 1773284901076163555567833)
                      ·
                        rfl

theorem cell23_3453460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_3453460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3453460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3453460 prefixEnd_3453460 := by exact prefixLift 3453460
  have htrace : WordTrace (prefixWord ++ tailWord_3453460) baseStart_3453460 baseEnd_3453460 := by
    simpa [prefixWord, tailWord_3453460, baseEnd_3453460] using wordTrace_append hprefix tailTrace_3453460
  have hstable : (prefixWord ++ tailWord_3453460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453460).length < 2 ^ (prefixWord ++ tailWord_3453460).sum := by decide
  have hdescent : baseEnd_3453460 < baseStart_3453460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453489 : List Nat := [1, 2, 2, 3, 1, 1, 2, 1, 4, 3, 3]
def baseStart_3453489 : Nat := 118140960795 + 3453489 * 2 ^ 59
def prefixEnd_3453489 : Nat := 4983230072969 + 3 ^ 40 * 3453489 * 2
def baseEnd_3453489 : Nat := 1773299792015143942105199

theorem tailTrace_3453489 : CollatzResearch.WordTrace tailWord_3453489 prefixEnd_3453489 1773299792015143942105199 := by
  unfold tailWord_3453489
  simp only [CollatzResearch.WordTrace]
  refine ⟨125959091785606636809219521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83972727857071091206146347 125959091785606636809219521)
  ·
    refine ⟨94469318839204977606914641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125959091785606636809219521 94469318839204977606914641)
    ·
      refine ⟨70851989129403733205185981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94469318839204977606914641 70851989129403733205185981)
      ·
        refine ⟨26569495923526399951944743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70851989129403733205185981 26569495923526399951944743)
        ·
          refine ⟨39854243885289599927917115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26569495923526399951944743 39854243885289599927917115)
          ·
            refine ⟨59781365827934399891875673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39854243885289599927917115 59781365827934399891875673)
            ·
              refine ⟨44836024370950799918906755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59781365827934399891875673 44836024370950799918906755)
              ·
                refine ⟨67254036556426199878360133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44836024370950799918906755 67254036556426199878360133)
                ·
                  refine ⟨12610131854329912477192525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67254036556426199878360133 12610131854329912477192525)
                  ·
                    refine ⟨4728799445373717178947197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12610131854329912477192525 4728799445373717178947197)
                    ·
                      refine ⟨1773299792015143942105199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4728799445373717178947197 1773299792015143942105199)
                      ·
                        rfl

theorem cell23_3453489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_3453489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3453489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3453489 prefixEnd_3453489 := by exact prefixLift 3453489
  have htrace : WordTrace (prefixWord ++ tailWord_3453489) baseStart_3453489 baseEnd_3453489 := by
    simpa [prefixWord, tailWord_3453489, baseEnd_3453489] using wordTrace_append hprefix tailTrace_3453489
  have hstable : (prefixWord ++ tailWord_3453489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453489).length < 2 ^ (prefixWord ++ tailWord_3453489).sum := by decide
  have hdescent : baseEnd_3453489 < baseStart_3453489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453546 : List Nat := [3, 1, 3, 2, 1, 1, 1, 4, 2, 1, 4]
def baseStart_3453546 : Nat := 118140960795 + 3453546 * 2 ^ 59
def prefixEnd_3453546 : Nat := 4983230072969 + 3 ^ 40 * 3453546 * 2
def baseEnd_3453546 : Nat := 1773329060412450219092437

theorem tailTrace_3453546 : CollatzResearch.WordTrace tailWord_3453546 prefixEnd_3453546 1773329060412450219092437 := by
  unfold tailWord_3453546
  simp only [CollatzResearch.WordTrace]
  refine ⟨31490292686600033886011123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83974113830933423696029661 31490292686600033886011123)
  ·
    refine ⟨47235439029900050829016685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31490292686600033886011123 47235439029900050829016685)
    ·
      refine ⟨17713289636212519060881257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47235439029900050829016685 17713289636212519060881257)
      ·
        refine ⟨13284967227159389295660943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17713289636212519060881257 13284967227159389295660943)
        ·
          refine ⟨19927450840739083943491415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13284967227159389295660943 19927450840739083943491415)
          ·
            refine ⟨29891176261108625915237123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19927450840739083943491415 29891176261108625915237123)
            ·
              refine ⟨44836764391662938872855685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29891176261108625915237123 44836764391662938872855685)
              ·
                refine ⟨8406893323436801038660441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44836764391662938872855685 8406893323436801038660441)
                ·
                  refine ⟨6305169992577600778995331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8406893323436801038660441 6305169992577600778995331)
                  ·
                    refine ⟨9457754988866401168492997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6305169992577600778995331 9457754988866401168492997)
                    ·
                      refine ⟨1773329060412450219092437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9457754988866401168492997 1773329060412450219092437)
                      ·
                        rfl

theorem cell23_3453546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_3453546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3453546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3453546 prefixEnd_3453546 := by exact prefixLift 3453546
  have htrace : WordTrace (prefixWord ++ tailWord_3453546) baseStart_3453546 baseEnd_3453546 := by
    simpa [prefixWord, tailWord_3453546, baseEnd_3453546] using wordTrace_append hprefix tailTrace_3453546
  have hstable : (prefixWord ++ tailWord_3453546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453546).length < 2 ^ (prefixWord ++ tailWord_3453546).sum := by decide
  have hdescent : baseEnd_3453546 < baseStart_3453546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453579 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 1, 7, 3]
def baseStart_3453579 : Nat := 118140960795 + 3453579 * 2 ^ 59
def prefixEnd_3453579 : Nat := 4983230072969 + 3 ^ 40 * 3453579 * 2
def baseEnd_3453579 : Nat := 1773346005274048589979785

theorem tailTrace_3453579 : CollatzResearch.WordTrace tailWord_3453579 prefixEnd_3453579 1773346005274048589979785 := by
  unfold tailWord_3453579
  simp only [CollatzResearch.WordTrace]
  refine ⟨125962374355280582179995791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83974916236853721453330527 125962374355280582179995791)
  ·
    refine ⟨188943561532920873269993687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125962374355280582179995791 188943561532920873269993687)
    ·
      refine ⟨283415342299381309904990531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188943561532920873269993687 283415342299381309904990531)
      ·
        refine ⟨425123013449071964857485797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283415342299381309904990531 425123013449071964857485797)
        ·
          refine ⟨79710565021700993410778587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 425123013449071964857485797 79710565021700993410778587)
          ·
            refine ⟨119565847532551490116167881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79710565021700993410778587 119565847532551490116167881)
            ·
              refine ⟨89674385649413617587125911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119565847532551490116167881 89674385649413617587125911)
              ·
                refine ⟨134511578474120426380688867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89674385649413617587125911 134511578474120426380688867)
                ·
                  refine ⟨201767367711180639571033301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134511578474120426380688867 201767367711180639571033301)
                  ·
                    refine ⟨4728922680730796239946093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 201767367711180639571033301 4728922680730796239946093)
                    ·
                      refine ⟨1773346005274048589979785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4728922680730796239946093 1773346005274048589979785)
                      ·
                        rfl

theorem cell23_3453579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 7, 3].length) (baseStart_3453579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3453579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3453579 prefixEnd_3453579 := by exact prefixLift 3453579
  have htrace : WordTrace (prefixWord ++ tailWord_3453579) baseStart_3453579 baseEnd_3453579 := by
    simpa [prefixWord, tailWord_3453579, baseEnd_3453579] using wordTrace_append hprefix tailTrace_3453579
  have hstable : (prefixWord ++ tailWord_3453579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453579).length < 2 ^ (prefixWord ++ tailWord_3453579).sum := by decide
  have hdescent : baseEnd_3453579 < baseStart_3453579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453656 : List Nat := [2, 1, 2, 2, 3, 2, 1, 3, 1, 1, 5]
def baseStart_3453656 : Nat := 118140960795 + 3453656 * 2 ^ 59
def prefixEnd_3453656 : Nat := 4983230072969 + 3 ^ 40 * 3453656 * 2
def baseEnd_3453656 : Nat := 1773385543284444788716931

theorem tailTrace_3453656 : CollatzResearch.WordTrace tailWord_3453656 prefixEnd_3453656 1773385543284444788716931 := by
  unfold tailWord_3453656
  simp only [CollatzResearch.WordTrace]
  refine ⟨62982591388000812165274411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83976788517334416220365881 62982591388000812165274411)
  ·
    refine ⟨94473887082001218247911617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62982591388000812165274411 94473887082001218247911617)
    ·
      refine ⟨70855415311500913685933713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94473887082001218247911617 70855415311500913685933713)
      ·
        refine ⟨53141561483625685264450285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70855415311500913685933713 53141561483625685264450285)
        ·
          refine ⟨19928085556359631974168857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53141561483625685264450285 19928085556359631974168857)
          ·
            refine ⟨14946064167269723980626643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19928085556359631974168857 14946064167269723980626643)
            ·
              refine ⟨22419096250904585970939965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14946064167269723980626643 22419096250904585970939965)
              ·
                refine ⟨8407161094089219739102487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22419096250904585970939965 8407161094089219739102487)
                ·
                  refine ⟨12610741641133829608653731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8407161094089219739102487 12610741641133829608653731)
                  ·
                    refine ⟨18916112461700744412980597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12610741641133829608653731 18916112461700744412980597)
                    ·
                      refine ⟨1773385543284444788716931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18916112461700744412980597 1773385543284444788716931)
                      ·
                        rfl

theorem cell23_3453656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_3453656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3453656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3453656 prefixEnd_3453656 := by exact prefixLift 3453656
  have htrace : WordTrace (prefixWord ++ tailWord_3453656) baseStart_3453656 baseEnd_3453656 := by
    simpa [prefixWord, tailWord_3453656, baseEnd_3453656] using wordTrace_append hprefix tailTrace_3453656
  have hstable : (prefixWord ++ tailWord_3453656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453656).length < 2 ^ (prefixWord ++ tailWord_3453656).sum := by decide
  have hdescent : baseEnd_3453656 < baseStart_3453656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3453684 : List Nat := [2, 6, 1, 1, 2, 2, 1, 2, 1, 5]
def baseStart_3453684 : Nat := 118140960795 + 3453684 * 2 ^ 59
def prefixEnd_3453684 : Nat := 4983230072969 + 3 ^ 40 * 3453684 * 2
def baseEnd_3453684 : Nat := 591133306914256893055601

theorem tailTrace_3453684 : CollatzResearch.WordTrace tailWord_3453684 prefixEnd_3453684 591133306914256893055601 := by
  unfold tailWord_3453684
  simp only [CollatzResearch.WordTrace]
  refine ⟨62983102009950092556284053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83977469346600123408378737 62983102009950092556284053)
  ·
    refine ⟨2952332906716410588575815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 62983102009950092556284053 2952332906716410588575815)
    ·
      refine ⟨4428499360074615882863723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2952332906716410588575815 4428499360074615882863723)
      ·
        refine ⟨6642749040111923824295585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4428499360074615882863723 6642749040111923824295585)
        ·
          refine ⟨4982061780083942868221689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6642749040111923824295585 4982061780083942868221689)
          ·
            refine ⟨3736546335062957151166267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4982061780083942868221689 3736546335062957151166267)
            ·
              refine ⟨5604819502594435726749401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3736546335062957151166267 5604819502594435726749401)
              ·
                refine ⟨4203614626945826795062051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5604819502594435726749401 4203614626945826795062051)
                ·
                  refine ⟨6305421940418740192593077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4203614626945826795062051 6305421940418740192593077)
                  ·
                    refine ⟨591133306914256893055601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6305421940418740192593077 591133306914256893055601)
                    ·
                      rfl

theorem cell23_3453684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_3453684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3453684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3453684 prefixEnd_3453684 := by exact prefixLift 3453684
  have htrace : WordTrace (prefixWord ++ tailWord_3453684) baseStart_3453684 baseEnd_3453684 := by
    simpa [prefixWord, tailWord_3453684, baseEnd_3453684] using wordTrace_append hprefix tailTrace_3453684
  have hstable : (prefixWord ++ tailWord_3453684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3453684).length < 2 ^ (prefixWord ++ tailWord_3453684).sum := by decide
  have hdescent : baseEnd_3453684 < baseStart_3453684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3453684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
