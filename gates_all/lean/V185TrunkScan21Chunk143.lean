import V185TrunkScan21Chunk142

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1743470 : List Nat := [4, 1, 2, 2, 2, 2, 3, 2, 3]
def baseStart_1743470 : Nat := 118140960795 + 1743470 * 2 ^ 59
def prefixEnd_1743470 : Nat := 4983230072969 + 3 ^ 40 * 1743470 * 2
def baseEnd_1743470 : Nat := 397883607419732844136415

theorem tailTrace_1743470 : CollatzResearch.WordTrace tailWord_1743470 prefixEnd_1743470 397883607419732844136415 := by
  unfold tailWord_1743470
  simp only [CollatzResearch.WordTrace]
  refine ⟨7948696874214178226893483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42393049995808950543431909 7948696874214178226893483)
  ·
    refine ⟨11923045311321267340340225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7948696874214178226893483 11923045311321267340340225)
    ·
      refine ⟨8942283983490950505255169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11923045311321267340340225 8942283983490950505255169)
      ·
        refine ⟨6706712987618212878941377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8942283983490950505255169 6706712987618212878941377)
        ·
          refine ⟨5030034740713659659206033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6706712987618212878941377 5030034740713659659206033)
          ·
            refine ⟨3772526055535244744404525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5030034740713659659206033 3772526055535244744404525)
            ·
              refine ⟨1414697270825716779151697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3772526055535244744404525 1414697270825716779151697)
              ·
                refine ⟨1061022953119287584363773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1414697270825716779151697 1061022953119287584363773)
                ·
                  refine ⟨397883607419732844136415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1061022953119287584363773 397883607419732844136415)
                  ·
                    rfl

theorem cell21_1743470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 2, 3].length) (baseStart_1743470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1743470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1743470 prefixEnd_1743470 := by exact prefixLift 1743470
  have htrace : WordTrace (prefixWord ++ tailWord_1743470) baseStart_1743470 baseEnd_1743470 := by
    simpa [prefixWord, tailWord_1743470, baseEnd_1743470] using wordTrace_append hprefix tailTrace_1743470
  have hstable : (prefixWord ++ tailWord_1743470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743470).length < 2 ^ (prefixWord ++ tailWord_1743470).sum := by decide
  have hdescent : baseEnd_1743470 < baseStart_1743470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743512 : List Nat := [2, 1, 2, 4, 1, 1, 2, 5, 3]
def baseStart_1743512 : Nat := 118140960795 + 1743512 * 2 ^ 59
def prefixEnd_1743512 : Nat := 4983230072969 + 3 ^ 40 * 1743512 * 2
def baseEnd_1743512 : Nat := 397893192391950104436329

theorem tailTrace_1743512 : CollatzResearch.WordTrace tailWord_1743512 prefixEnd_1743512 397893192391950104436329 := by
  unfold tailWord_1743512
  simp only [CollatzResearch.WordTrace]
  refine ⟨31795553429780633494088395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42394071239707511325451193 31795553429780633494088395)
  ·
    refine ⟨47693330144670950241132593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31795553429780633494088395 47693330144670950241132593)
    ·
      refine ⟨35769997608503212680849445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47693330144670950241132593 35769997608503212680849445)
      ·
        refine ⟨6706874551594352377659271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35769997608503212680849445 6706874551594352377659271)
        ·
          refine ⟨10060311827391528566488907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6706874551594352377659271 10060311827391528566488907)
          ·
            refine ⟨15090467741087292849733361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10060311827391528566488907 15090467741087292849733361)
            ·
              refine ⟨11317850805815469637300021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15090467741087292849733361 11317850805815469637300021)
              ·
                refine ⟨1061048513045200278496877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11317850805815469637300021 1061048513045200278496877)
                ·
                  refine ⟨397893192391950104436329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1061048513045200278496877 397893192391950104436329)
                  ·
                    rfl

theorem cell21_1743512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 5, 3].length) (baseStart_1743512 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1743512 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1743512 prefixEnd_1743512 := by exact prefixLift 1743512
  have htrace : WordTrace (prefixWord ++ tailWord_1743512) baseStart_1743512 baseEnd_1743512 := by
    simpa [prefixWord, tailWord_1743512, baseEnd_1743512] using wordTrace_append hprefix tailTrace_1743512
  have hstable : (prefixWord ++ tailWord_1743512).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743512).length < 2 ^ (prefixWord ++ tailWord_1743512).sum := by decide
  have hdescent : baseEnd_1743512 < baseStart_1743512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743588 : List Nat := [2, 3, 1, 1, 1, 4, 2, 4, 3]
def baseStart_1743588 : Nat := 118140960795 + 1743588 * 2 ^ 59
def prefixEnd_1743588 : Nat := 4983230072969 + 3 ^ 40 * 1743588 * 2
def baseEnd_1743588 : Nat := 397910536627390861169507

theorem tailTrace_1743588 : CollatzResearch.WordTrace tailWord_1743588 prefixEnd_1743588 397910536627390861169507 := by
  unfold tailWord_1743588
  simp only [CollatzResearch.WordTrace]
  refine ⟨31796939403642965983971709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42395919204857287978628945 31796939403642965983971709)
  ·
    refine ⟨11923852276366112243989391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31796939403642965983971709 11923852276366112243989391)
    ·
      refine ⟨17885778414549168365984087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11923852276366112243989391 17885778414549168365984087)
      ·
        refine ⟨26828667621823752548976131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17885778414549168365984087 26828667621823752548976131)
        ·
          refine ⟨40243001432735628823464197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26828667621823752548976131 40243001432735628823464197)
          ·
            refine ⟨7545562768637930404399537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40243001432735628823464197 7545562768637930404399537)
            ·
              refine ⟨5659172076478447803299653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7545562768637930404399537 5659172076478447803299653)
              ·
                refine ⟨1061094764339708963118685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5659172076478447803299653 1061094764339708963118685)
                ·
                  refine ⟨397910536627390861169507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1061094764339708963118685 397910536627390861169507)
                  ·
                    rfl

theorem cell21_1743588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 4, 3].length) (baseStart_1743588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1743588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1743588 prefixEnd_1743588 := by exact prefixLift 1743588
  have htrace : WordTrace (prefixWord ++ tailWord_1743588) baseStart_1743588 baseEnd_1743588 := by
    simpa [prefixWord, tailWord_1743588, baseEnd_1743588] using wordTrace_append hprefix tailTrace_1743588
  have hstable : (prefixWord ++ tailWord_1743588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743588).length < 2 ^ (prefixWord ++ tailWord_1743588).sum := by decide
  have hdescent : baseEnd_1743588 < baseStart_1743588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743647 : List Nat := [1, 1, 2, 4, 2, 2, 3, 1, 5]
def baseStart_1743647 : Nat := 118140960795 + 1743647 * 2 ^ 59
def prefixEnd_1743647 : Nat := 4983230072969 + 3 ^ 40 * 1743647 * 2
def baseEnd_1743647 : Nat := 397924001231219869686053

theorem tailTrace_1743647 : CollatzResearch.WordTrace tailWord_1743647 prefixEnd_1743647 397924001231219869686053 := by
  unfold tailWord_1743647
  simp only [CollatzResearch.WordTrace]
  refine ⟨63596030714072185044341195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42397353809381456696227463 63596030714072185044341195)
  ·
    refine ⟨95394046071108277566511793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63596030714072185044341195 95394046071108277566511793)
    ·
      refine ⟨71545534553331208174883845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95394046071108277566511793 71545534553331208174883845)
      ·
        refine ⟨13414787728749601532790721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71545534553331208174883845 13414787728749601532790721)
        ·
          refine ⟨10061090796562201149593041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13414787728749601532790721 10061090796562201149593041)
          ·
            refine ⟨7545818097421650862194781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10061090796562201149593041 7545818097421650862194781)
            ·
              refine ⟨2829681786533119073323043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7545818097421650862194781 2829681786533119073323043)
              ·
                refine ⟨4244522679799678609984565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2829681786533119073323043 4244522679799678609984565)
                ·
                  refine ⟨397924001231219869686053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4244522679799678609984565 397924001231219869686053)
                  ·
                    rfl

theorem cell21_1743647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 5].length) (baseStart_1743647 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1743647 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1743647 prefixEnd_1743647 := by exact prefixLift 1743647
  have htrace : WordTrace (prefixWord ++ tailWord_1743647) baseStart_1743647 baseEnd_1743647 := by
    simpa [prefixWord, tailWord_1743647, baseEnd_1743647] using wordTrace_append hprefix tailTrace_1743647
  have hstable : (prefixWord ++ tailWord_1743647).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743647).length < 2 ^ (prefixWord ++ tailWord_1743647).sum := by decide
  have hdescent : baseEnd_1743647 < baseStart_1743647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743726 : List Nat := [4, 1, 2, 3, 2, 1, 3, 5]
def baseStart_1743726 : Nat := 118140960795 + 1743726 * 2 ^ 59
def prefixEnd_1743726 : Nat := 4983230072969 + 3 ^ 40 * 1743726 * 2
def baseEnd_1743726 : Nat := 132647343369177762623075

theorem tailTrace_1743726 : CollatzResearch.WordTrace tailWord_1743726 prefixEnd_1743726 132647343369177762623075 := by
  unfold tailWord_1743726
  simp only [CollatzResearch.WordTrace]
  refine ⟨7949864010098247692058379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42399274720523987690978021 7949864010098247692058379)
  ·
    refine ⟨11924796015147371538087569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7949864010098247692058379 11924796015147371538087569)
    ·
      refine ⟨8943597011360528653565677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11924796015147371538087569 8943597011360528653565677)
      ·
        refine ⟨3353848879260198245087129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8943597011360528653565677 3353848879260198245087129)
        ·
          refine ⟨2515386659445148683815347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3353848879260198245087129 2515386659445148683815347)
          ·
            refine ⟨3773079989167723025723021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2515386659445148683815347 3773079989167723025723021)
            ·
              refine ⟨1414904995937896134646133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3773079989167723025723021 1414904995937896134646133)
              ·
                refine ⟨132647343369177762623075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1414904995937896134646133 132647343369177762623075)
                ·
                  rfl

theorem cell21_1743726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 5].length) (baseStart_1743726 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1743726 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1743726 prefixEnd_1743726 := by exact prefixLift 1743726
  have htrace : WordTrace (prefixWord ++ tailWord_1743726) baseStart_1743726 baseEnd_1743726 := by
    simpa [prefixWord, tailWord_1743726, baseEnd_1743726] using wordTrace_append hprefix tailTrace_1743726
  have hstable : (prefixWord ++ tailWord_1743726).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743726).length < 2 ^ (prefixWord ++ tailWord_1743726).sum := by decide
  have hdescent : baseEnd_1743726 < baseStart_1743726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743746 : List Nat := [3, 4, 2, 2, 2, 1, 1, 2, 4]
def baseStart_1743746 : Nat := 118140960795 + 1743746 * 2 ^ 59
def prefixEnd_1743746 : Nat := 4983230072969 + 3 ^ 40 * 1743746 * 2
def baseEnd_1743746 : Nat := 397946594380017697535851

theorem tailTrace_1743746 : CollatzResearch.WordTrace tailWord_1743746 prefixEnd_1743746 397946594380017697535851 := by
  unfold tailWord_1743746
  simp only [CollatzResearch.WordTrace]
  refine ⟨15899910385178381238048773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42399761027142349968130061 15899910385178381238048773)
  ·
    refine ⟨2981233197220946482134145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15899910385178381238048773 2981233197220946482134145)
    ·
      refine ⟨2235924897915709861600609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2981233197220946482134145 2235924897915709861600609)
      ·
        refine ⟨1676943673436782396200457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2235924897915709861600609 1676943673436782396200457)
        ·
          refine ⟨1257707755077586797150343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1676943673436782396200457 1257707755077586797150343)
          ·
            refine ⟨1886561632616380195725515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1257707755077586797150343 1886561632616380195725515)
            ·
              refine ⟨2829842448924570293588273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1886561632616380195725515 2829842448924570293588273)
              ·
                refine ⟨2122381836693427720191205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2829842448924570293588273 2122381836693427720191205)
                ·
                  refine ⟨397946594380017697535851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2122381836693427720191205 397946594380017697535851)
                  ·
                    rfl

theorem cell21_1743746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_1743746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1743746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1743746 prefixEnd_1743746 := by exact prefixLift 1743746
  have htrace : WordTrace (prefixWord ++ tailWord_1743746) baseStart_1743746 baseEnd_1743746 := by
    simpa [prefixWord, tailWord_1743746, baseEnd_1743746] using wordTrace_append hprefix tailTrace_1743746
  have hstable : (prefixWord ++ tailWord_1743746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743746).length < 2 ^ (prefixWord ++ tailWord_1743746).sum := by decide
  have hdescent : baseEnd_1743746 < baseStart_1743746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743754 : List Nat := [3, 1, 2, 4, 1, 2, 1, 1, 6]
def baseStart_1743754 : Nat := 118140960795 + 1743754 * 2 ^ 59
def prefixEnd_1743754 : Nat := 4983230072969 + 3 ^ 40 * 1743754 * 2
def baseEnd_1743754 : Nat := 397948420089011461402501

theorem tailTrace_1743754 : CollatzResearch.WordTrace tailWord_1743754 prefixEnd_1743754 397948420089011461402501 := by
  unfold tailWord_1743754
  simp only [CollatzResearch.WordTrace]
  refine ⟨15899983331171135579621579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42399955549789694878990877 15899983331171135579621579)
  ·
    refine ⟨23849974996756703369432369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15899983331171135579621579 23849974996756703369432369)
    ·
      refine ⟨17887481247567527527074277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23849974996756703369432369 17887481247567527527074277)
      ·
        refine ⟨3353902733918911411326427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17887481247567527527074277 3353902733918911411326427)
        ·
          refine ⟨5030854100878367116989641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3353902733918911411326427 5030854100878367116989641)
          ·
            refine ⟨3773140575658775337742231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5030854100878367116989641 3773140575658775337742231)
            ·
              refine ⟨5659710863488163006613347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3773140575658775337742231 5659710863488163006613347)
              ·
                refine ⟨8489566295232244509920021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5659710863488163006613347 8489566295232244509920021)
                ·
                  refine ⟨397948420089011461402501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8489566295232244509920021 397948420089011461402501)
                  ·
                    rfl

theorem cell21_1743754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 6].length) (baseStart_1743754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1743754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1743754 prefixEnd_1743754 := by exact prefixLift 1743754
  have htrace : WordTrace (prefixWord ++ tailWord_1743754) baseStart_1743754 baseEnd_1743754 := by
    simpa [prefixWord, tailWord_1743754, baseEnd_1743754] using wordTrace_append hprefix tailTrace_1743754
  have hstable : (prefixWord ++ tailWord_1743754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743754).length < 2 ^ (prefixWord ++ tailWord_1743754).sum := by decide
  have hdescent : baseEnd_1743754 < baseStart_1743754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743816 : List Nat := [2, 1, 3, 1, 5, 2, 1, 1, 5]
def baseStart_1743816 : Nat := 118140960795 + 1743816 * 2 ^ 59
def prefixEnd_1743816 : Nat := 4983230072969 + 3 ^ 40 * 1743816 * 2
def baseEnd_1743816 : Nat := 397962569333713131369041

theorem tailTrace_1743816 : CollatzResearch.WordTrace tailWord_1743816 prefixEnd_1743816 397962569333713131369041 := by
  unfold tailWord_1743816
  simp only [CollatzResearch.WordTrace]
  refine ⟨31801097325229963453621651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42401463100306617938162201 31801097325229963453621651)
  ·
    refine ⟨47701645987844945180432477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31801097325229963453621651 47701645987844945180432477)
    ·
      refine ⟨17888117245441854442662179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47701645987844945180432477 17888117245441854442662179)
      ·
        refine ⟨26832175868162781663993269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17888117245441854442662179 26832175868162781663993269)
        ·
          refine ⟨2515516487640260780999369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26832175868162781663993269 2515516487640260780999369)
          ·
            refine ⟨1886637365730195585749527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2515516487640260780999369 1886637365730195585749527)
            ·
              refine ⟨2829956048595293378624291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1886637365730195585749527 2829956048595293378624291)
              ·
                refine ⟨4244934072892940067936437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2829956048595293378624291 4244934072892940067936437)
                ·
                  refine ⟨397962569333713131369041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4244934072892940067936437 397962569333713131369041)
                  ·
                    rfl

theorem cell21_1743816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 5].length) (baseStart_1743816 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1743816 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1743816 prefixEnd_1743816 := by exact prefixLift 1743816
  have htrace : WordTrace (prefixWord ++ tailWord_1743816) baseStart_1743816 baseEnd_1743816 := by
    simpa [prefixWord, tailWord_1743816, baseEnd_1743816] using wordTrace_append hprefix tailTrace_1743816
  have hstable : (prefixWord ++ tailWord_1743816).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743816).length < 2 ^ (prefixWord ++ tailWord_1743816).sum := by decide
  have hdescent : baseEnd_1743816 < baseStart_1743816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743861 : List Nat := [1, 3, 5, 2, 1, 9]
def baseStart_1743861 : Nat := 118140960795 + 1743861 * 2 ^ 59
def prefixEnd_1743861 : Nat := 4983230072969 + 3 ^ 40 * 1743861 * 2
def baseEnd_1743861 : Nat := 14739734775807520485887

theorem tailTrace_1743861 : CollatzResearch.WordTrace tailWord_1743861 prefixEnd_1743861 14739734775807520485887 := by
  unfold tailWord_1743861
  simp only [CollatzResearch.WordTrace]
  refine ⟨63603835935296899592631437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42402557290197933061754291 63603835935296899592631437)
  ·
    refine ⟨23851438475736337347236789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63603835935296899592631437 23851438475736337347236789)
    ·
      refine ⟨2236072357100281626303449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23851438475736337347236789 2236072357100281626303449)
      ·
        refine ⟨1677054267825211219727587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2236072357100281626303449 1677054267825211219727587)
        ·
          refine ⟨2515581401737816829591381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1677054267825211219727587 2515581401737816829591381)
          ·
            refine ⟨14739734775807520485887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2515581401737816829591381 14739734775807520485887)
            ·
              rfl

theorem cell21_1743861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 9].length) (baseStart_1743861 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1743861 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1743861 prefixEnd_1743861 := by exact prefixLift 1743861
  have htrace : WordTrace (prefixWord ++ tailWord_1743861) baseStart_1743861 baseEnd_1743861 := by
    simpa [prefixWord, tailWord_1743861, baseEnd_1743861] using wordTrace_append hprefix tailTrace_1743861
  have hstable : (prefixWord ++ tailWord_1743861).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743861).length < 2 ^ (prefixWord ++ tailWord_1743861).sum := by decide
  have hdescent : baseEnd_1743861 < baseStart_1743861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743872 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 10]
def baseStart_1743872 : Nat := 118140960795 + 1743872 * 2 ^ 59
def prefixEnd_1743872 : Nat := 4983230072969 + 3 ^ 40 * 1743872 * 2
def baseEnd_1743872 : Nat := 397975349296669478435593

theorem tailTrace_1743872 : CollatzResearch.WordTrace tailWord_1743872 prefixEnd_1743872 397975349296669478435593 := by
  unfold tailWord_1743872
  simp only [CollatzResearch.WordTrace]
  refine ⟨31802118569128524235640935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42402824758838032314187913 31802118569128524235640935)
  ·
    refine ⟨47703177853692786353461403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31802118569128524235640935 47703177853692786353461403)
    ·
      refine ⟨71554766780539179530192105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47703177853692786353461403 71554766780539179530192105)
      ·
        refine ⟨53666075085404384647644079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71554766780539179530192105 53666075085404384647644079)
        ·
          refine ⟨80499112628106576971466119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53666075085404384647644079 80499112628106576971466119)
          ·
            refine ⟨120748668942159865457199179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80499112628106576971466119 120748668942159865457199179)
            ·
              refine ⟨181123003413239798185798769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120748668942159865457199179 181123003413239798185798769)
              ·
                refine ⟨135842252559929848639349077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181123003413239798185798769 135842252559929848639349077)
                ·
                  refine ⟨397975349296669478435593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 135842252559929848639349077 397975349296669478435593)
                  ·
                    rfl

theorem cell21_1743872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 10].length) (baseStart_1743872 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1743872 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1743872 prefixEnd_1743872 := by exact prefixLift 1743872
  have htrace : WordTrace (prefixWord ++ tailWord_1743872) baseStart_1743872 baseEnd_1743872 := by
    simpa [prefixWord, tailWord_1743872, baseEnd_1743872] using wordTrace_append hprefix tailTrace_1743872
  have hstable : (prefixWord ++ tailWord_1743872).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743872).length < 2 ^ (prefixWord ++ tailWord_1743872).sum := by decide
  have hdescent : baseEnd_1743872 < baseStart_1743872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744010 : List Nat := [3, 1, 2, 3, 1, 1, 2, 1, 7]
def baseStart_1744010 : Nat := 118140960795 + 1744010 * 2 ^ 59
def prefixEnd_1744010 : Nat := 4983230072969 + 3 ^ 40 * 1744010 * 2
def baseEnd_1744010 : Nat := 398006842776811905135311

theorem tailTrace_1744010 : CollatzResearch.WordTrace tailWord_1744010 prefixEnd_1744010 398006842776811905135311 := by
  unfold tailWord_1744010
  simp only [CollatzResearch.WordTrace]
  refine ⟨15902317602939274509951371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42406180274504732026536989 15902317602939274509951371)
  ·
    refine ⟨23853476404408911764927057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15902317602939274509951371 23853476404408911764927057)
    ·
      refine ⟨17890107303306683823695293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23853476404408911764927057 17890107303306683823695293)
      ·
        refine ⟨6708790238740006433885735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17890107303306683823695293 6708790238740006433885735)
        ·
          refine ⟨10063185358110009650828603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6708790238740006433885735 10063185358110009650828603)
          ·
            refine ⟨15094778037165014476242905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10063185358110009650828603 15094778037165014476242905)
            ·
              refine ⟨11321083527873760857182179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15094778037165014476242905 11321083527873760857182179)
              ·
                refine ⟨16981625291810641285773269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11321083527873760857182179 16981625291810641285773269)
                ·
                  refine ⟨398006842776811905135311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16981625291810641285773269 398006842776811905135311)
                  ·
                    rfl

theorem cell21_1744010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 7].length) (baseStart_1744010 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1744010 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1744010 prefixEnd_1744010 := by exact prefixLift 1744010
  have htrace : WordTrace (prefixWord ++ tailWord_1744010) baseStart_1744010 baseEnd_1744010 := by
    simpa [prefixWord, tailWord_1744010, baseEnd_1744010] using wordTrace_append hprefix tailTrace_1744010
  have hstable : (prefixWord ++ tailWord_1744010).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744010).length < 2 ^ (prefixWord ++ tailWord_1744010).sum := by decide
  have hdescent : baseEnd_1744010 < baseStart_1744010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744131 : List Nat := [1, 1, 1, 3, 2, 5, 1, 7]
def baseStart_1744131 : Nat := 118140960795 + 1744131 * 2 ^ 59
def prefixEnd_1744131 : Nat := 4983230072969 + 3 ^ 40 * 1744131 * 2
def baseEnd_1744131 : Nat := 132678152208447527872799

theorem tailTrace_1744131 : CollatzResearch.WordTrace tailWord_1744131 prefixEnd_1744131 132678152208447527872799 := by
  unfold tailWord_1744131
  simp only [CollatzResearch.WordTrace]
  refine ⟨63613683644318735704960247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42409122429545823803306831 63613683644318735704960247)
  ·
    refine ⟨95420525466478103557440371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63613683644318735704960247 95420525466478103557440371)
    ·
      refine ⟨143130788199717155336160557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95420525466478103557440371 143130788199717155336160557)
      ·
        refine ⟨53674045574893933251060209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143130788199717155336160557 53674045574893933251060209)
        ·
          refine ⟨40255534181170449938295157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53674045574893933251060209 40255534181170449938295157)
          ·
            refine ⟨3773956329484729681715171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40255534181170449938295157 3773956329484729681715171)
            ·
              refine ⟨5660934494227094522572757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3773956329484729681715171 5660934494227094522572757)
              ·
                refine ⟨132678152208447527872799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5660934494227094522572757 132678152208447527872799)
                ·
                  rfl

theorem cell21_1744131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 7].length) (baseStart_1744131 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1744131 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1744131 prefixEnd_1744131 := by exact prefixLift 1744131
  have htrace : WordTrace (prefixWord ++ tailWord_1744131) baseStart_1744131 baseEnd_1744131 := by
    simpa [prefixWord, tailWord_1744131, baseEnd_1744131] using wordTrace_append hprefix tailTrace_1744131
  have hstable : (prefixWord ++ tailWord_1744131).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744131).length < 2 ^ (prefixWord ++ tailWord_1744131).sum := by decide
  have hdescent : baseEnd_1744131 < baseStart_1744131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744213 : List Nat := [1, 3, 2, 2, 3, 3, 2, 2, 3]
def baseStart_1744213 : Nat := 118140960795 + 1744213 * 2 ^ 59
def prefixEnd_1744213 : Nat := 4983230072969 + 3 ^ 40 * 1744213 * 2
def baseEnd_1744213 : Nat := 398053170142528663251563

theorem tailTrace_1744213 : CollatzResearch.WordTrace tailWord_1744213 prefixEnd_1744213 398053170142528663251563 := by
  unfold tailWord_1744213
  simp only [CollatzResearch.WordTrace]
  refine ⟨63616674430021663709445293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42411116286681109139630195 63616674430021663709445293)
  ·
    refine ⟨23856252911258123891041985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63616674430021663709445293 23856252911258123891041985)
    ·
      refine ⟨17892189683443592918281489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23856252911258123891041985 17892189683443592918281489)
      ·
        refine ⟨13419142262582694688711117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17892189683443592918281489 13419142262582694688711117)
        ·
          refine ⟨5032178348468510508266669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13419142262582694688711117 5032178348468510508266669)
          ·
            refine ⟨1887066880675691440600001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5032178348468510508266669 1887066880675691440600001)
            ·
              refine ⟨1415300160506768580450001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1887066880675691440600001 1415300160506768580450001)
              ·
                refine ⟨1061475120380076435337501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1415300160506768580450001 1061475120380076435337501)
                ·
                  refine ⟨398053170142528663251563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1061475120380076435337501 398053170142528663251563)
                  ·
                    rfl

theorem cell21_1744213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 2, 3].length) (baseStart_1744213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1744213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1744213 prefixEnd_1744213 := by exact prefixLift 1744213
  have htrace : WordTrace (prefixWord ++ tailWord_1744213) baseStart_1744213 baseEnd_1744213 := by
    simpa [prefixWord, tailWord_1744213, baseEnd_1744213] using wordTrace_append hprefix tailTrace_1744213
  have hstable : (prefixWord ++ tailWord_1744213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744213).length < 2 ^ (prefixWord ++ tailWord_1744213).sum := by decide
  have hdescent : baseEnd_1744213 < baseStart_1744213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744224 : List Nat := [2, 1, 1, 3, 4, 3, 1, 6]
def baseStart_1744224 : Nat := 118140960795 + 1744224 * 2 ^ 59
def prefixEnd_1744224 : Nat := 4983230072969 + 3 ^ 40 * 1744224 * 2
def baseEnd_1744224 : Nat := 132685226830798362856069

theorem tailTrace_1744224 : CollatzResearch.WordTrace tailWord_1744224 prefixEnd_1744224 132685226830798362856069 := by
  unfold tailWord_1744224
  simp only [CollatzResearch.WordTrace]
  refine ⟨31808537816490906294047863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42411383755321208392063817 31808537816490906294047863)
  ·
    refine ⟨47712806724736359441071795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31808537816490906294047863 47712806724736359441071795)
    ·
      refine ⟨71569210087104539161607693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47712806724736359441071795 71569210087104539161607693)
      ·
        refine ⟨26838453782664202185602885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71569210087104539161607693 26838453782664202185602885)
        ·
          refine ⟨5032210084249537909800541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26838453782664202185602885 5032210084249537909800541)
          ·
            refine ⟨1887078781593576716175203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5032210084249537909800541 1887078781593576716175203)
            ·
              refine ⟨2830618172390365074262805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1887078781593576716175203 2830618172390365074262805)
              ·
                refine ⟨132685226830798362856069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2830618172390365074262805 132685226830798362856069)
                ·
                  rfl

theorem cell21_1744224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 6].length) (baseStart_1744224 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1744224 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1744224 prefixEnd_1744224 := by exact prefixLift 1744224
  have htrace : WordTrace (prefixWord ++ tailWord_1744224) baseStart_1744224 baseEnd_1744224 := by
    simpa [prefixWord, tailWord_1744224, baseEnd_1744224] using wordTrace_append hprefix tailTrace_1744224
  have hstable : (prefixWord ++ tailWord_1744224).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744224).length < 2 ^ (prefixWord ++ tailWord_1744224).sum := by decide
  have hdescent : baseEnd_1744224 < baseStart_1744224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744252 : List Nat := [2, 2, 2, 1, 1, 1, 4, 2, 6]
def baseStart_1744252 : Nat := 118140960795 + 1744252 * 2 ^ 59
def prefixEnd_1744252 : Nat := 4983230072969 + 3 ^ 40 * 1744252 * 2
def baseEnd_1744252 : Nat := 398062070473873262101483

theorem tailTrace_1744252 : CollatzResearch.WordTrace tailWord_1744252 prefixEnd_1744252 398062070473873262101483 := by
  unfold tailWord_1744252
  simp only [CollatzResearch.WordTrace]
  refine ⟨31809048438440186685057505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42412064584586915580076673 31809048438440186685057505)
  ·
    refine ⟨23856786328830140013793129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31809048438440186685057505 23856786328830140013793129)
    ·
      refine ⟨17892589746622605010344847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23856786328830140013793129 17892589746622605010344847)
      ·
        refine ⟨26838884619933907515517271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17892589746622605010344847 26838884619933907515517271)
        ·
          refine ⟨40258326929900861273275907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26838884619933907515517271 40258326929900861273275907)
          ·
            refine ⟨60387490394851291909913861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40258326929900861273275907 60387490394851291909913861)
            ·
              refine ⟨11322654449034617233108849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60387490394851291909913861 11322654449034617233108849)
              ·
                refine ⟨8491990836775962924831637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11322654449034617233108849 8491990836775962924831637)
                ·
                  refine ⟨398062070473873262101483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8491990836775962924831637 398062070473873262101483)
                  ·
                    rfl

theorem cell21_1744252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 6].length) (baseStart_1744252 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1744252 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1744252 prefixEnd_1744252 := by exact prefixLift 1744252
  have htrace : WordTrace (prefixWord ++ tailWord_1744252) baseStart_1744252 baseEnd_1744252 := by
    simpa [prefixWord, tailWord_1744252, baseEnd_1744252] using wordTrace_append hprefix tailTrace_1744252
  have hstable : (prefixWord ++ tailWord_1744252).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744252).length < 2 ^ (prefixWord ++ tailWord_1744252).sum := by decide
  have hdescent : baseEnd_1744252 < baseStart_1744252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744328 : List Nat := [2, 1, 3, 1, 3, 1, 1, 3, 6]
def baseStart_1744328 : Nat := 118140960795 + 1744328 * 2 ^ 59
def prefixEnd_1744328 : Nat := 4983230072969 + 3 ^ 40 * 1744328 * 2
def baseEnd_1744328 : Nat := 398079414709314018834661

theorem tailTrace_1744328 : CollatzResearch.WordTrace tailWord_1744328 prefixEnd_1744328 398079414709314018834661 := by
  unfold tailWord_1744328
  simp only [CollatzResearch.WordTrace]
  refine ⟨31810434412302519174940819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42413912549736692233254425 31810434412302519174940819)
  ·
    refine ⟨47715651618453778762411229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31810434412302519174940819 47715651618453778762411229)
    ·
      refine ⟨17893369356920167035904211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47715651618453778762411229 17893369356920167035904211)
      ·
        refine ⟨26840054035380250553856317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17893369356920167035904211 26840054035380250553856317)
        ·
          refine ⟨10065020263267593957696119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26840054035380250553856317 10065020263267593957696119)
          ·
            refine ⟨15097530394901390936544179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10065020263267593957696119 15097530394901390936544179)
            ·
              refine ⟨22646295592352086404816269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15097530394901390936544179 22646295592352086404816269)
              ·
                refine ⟨8492360847132032401806101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22646295592352086404816269 8492360847132032401806101)
                ·
                  refine ⟨398079414709314018834661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8492360847132032401806101 398079414709314018834661)
                  ·
                    rfl

theorem cell21_1744328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 6].length) (baseStart_1744328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1744328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1744328 prefixEnd_1744328 := by exact prefixLift 1744328
  have htrace : WordTrace (prefixWord ++ tailWord_1744328) baseStart_1744328 baseEnd_1744328 := by
    simpa [prefixWord, tailWord_1744328, baseEnd_1744328] using wordTrace_append hprefix tailTrace_1744328
  have hstable : (prefixWord ++ tailWord_1744328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744328).length < 2 ^ (prefixWord ++ tailWord_1744328).sum := by decide
  have hdescent : baseEnd_1744328 < baseStart_1744328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744345 : List Nat := [1, 2, 1, 2, 4, 3, 1, 3, 4]
def baseStart_1744345 : Nat := 118140960795 + 1744345 * 2 ^ 59
def prefixEnd_1744345 : Nat := 4983230072969 + 3 ^ 40 * 1744345 * 2
def baseEnd_1744345 : Nat := 398083294340925767051293

theorem tailTrace_1744345 : CollatzResearch.WordTrace tailWord_1744345 prefixEnd_1744345 398083294340925767051293 := by
  unfold tailWord_1744345
  simp only [CollatzResearch.WordTrace]
  refine ⟨63621488865543450253250489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42414325910362300168833659 63621488865543450253250489)
  ·
    refine ⟨47716116649157587689937867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63621488865543450253250489 47716116649157587689937867)
    ·
      refine ⟨71574174973736381534906801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47716116649157587689937867 71574174973736381534906801)
      ·
        refine ⟨53680631230302286151180101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71574174973736381534906801 53680631230302286151180101)
        ·
          refine ⟨10065118355681678653346269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53680631230302286151180101 10065118355681678653346269)
          ·
            refine ⟨3774419383380629495004851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10065118355681678653346269 3774419383380629495004851)
            ·
              refine ⟨5661629075070944242507277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3774419383380629495004851 5661629075070944242507277)
              ·
                refine ⟨2123110903151604090940229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5661629075070944242507277 2123110903151604090940229)
                ·
                  refine ⟨398083294340925767051293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2123110903151604090940229 398083294340925767051293)
                  ·
                    rfl

theorem cell21_1744345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 3, 4].length) (baseStart_1744345 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1744345 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1744345 prefixEnd_1744345 := by exact prefixLift 1744345
  have htrace : WordTrace (prefixWord ++ tailWord_1744345) baseStart_1744345 baseEnd_1744345 := by
    simpa [prefixWord, tailWord_1744345, baseEnd_1744345] using wordTrace_append hprefix tailTrace_1744345
  have hstable : (prefixWord ++ tailWord_1744345).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744345).length < 2 ^ (prefixWord ++ tailWord_1744345).sum := by decide
  have hdescent : baseEnd_1744345 < baseStart_1744345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744359 : List Nat := [1, 1, 5, 2, 1, 2, 2, 7]
def baseStart_1744359 : Nat := 118140960795 + 1744359 * 2 ^ 59
def prefixEnd_1744359 : Nat := 4983230072969 + 3 ^ 40 * 1744359 * 2
def baseEnd_1744359 : Nat := 132695496443888284605977

theorem tailTrace_1744359 : CollatzResearch.WordTrace tailWord_1744359 prefixEnd_1744359 132695496443888284605977 := by
  unfold tailWord_1744359
  simp only [CollatzResearch.WordTrace]
  refine ⟨63621999487492730644260131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42414666324995153762840087 63621999487492730644260131)
  ·
    refine ⟨95432999231239095966390197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63621999487492730644260131 95432999231239095966390197)
    ·
      refine ⟨8946843677928665246849081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95432999231239095966390197 8946843677928665246849081)
      ·
        refine ⟨6710132758446498935136811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8946843677928665246849081 6710132758446498935136811)
        ·
          refine ⟨10065199137669748402705217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6710132758446498935136811 10065199137669748402705217)
          ·
            refine ⟨7548899353252311302028913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10065199137669748402705217 7548899353252311302028913)
            ·
              refine ⟨5661674514939233476521685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7548899353252311302028913 5661674514939233476521685)
              ·
                refine ⟨132695496443888284605977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5661674514939233476521685 132695496443888284605977)
                ·
                  rfl

theorem cell21_1744359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 7].length) (baseStart_1744359 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1744359 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1744359 prefixEnd_1744359 := by exact prefixLift 1744359
  have htrace : WordTrace (prefixWord ++ tailWord_1744359) baseStart_1744359 baseEnd_1744359 := by
    simpa [prefixWord, tailWord_1744359, baseEnd_1744359] using wordTrace_append hprefix tailTrace_1744359
  have hstable : (prefixWord ++ tailWord_1744359).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744359).length < 2 ^ (prefixWord ++ tailWord_1744359).sum := by decide
  have hdescent : baseEnd_1744359 < baseStart_1744359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744438 : List Nat := [5, 1, 2, 1, 3, 1, 1, 1, 6]
def baseStart_1744438 : Nat := 118140960795 + 1744438 * 2 ^ 59
def prefixEnd_1744438 : Nat := 4983230072969 + 3 ^ 40 * 1744438 * 2
def baseEnd_1744438 : Nat := 398104518207978272001103

theorem tailTrace_1744438 : CollatzResearch.WordTrace tailWord_1744438 prefixEnd_1744438 398104518207978272001103 := by
  unfold tailWord_1744438
  simp only [CollatzResearch.WordTrace]
  refine ⟨3976555053387907946024123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42416587236137684757590645 3976555053387907946024123)
  ·
    refine ⟨5964832580081861919036185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3976555053387907946024123 5964832580081861919036185)
    ·
      refine ⟨4473624435061396439277139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5964832580081861919036185 4473624435061396439277139)
      ·
        refine ⟨6710436652592094658915709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4473624435061396439277139 6710436652592094658915709)
        ·
          refine ⟨2516413744722035497093391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6710436652592094658915709 2516413744722035497093391)
          ·
            refine ⟨3774620617083053245640087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2516413744722035497093391 3774620617083053245640087)
            ·
              refine ⟨5661930925624579868460131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3774620617083053245640087 5661930925624579868460131)
              ·
                refine ⟨8492896388436869802690197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5661930925624579868460131 8492896388436869802690197)
                ·
                  refine ⟨398104518207978272001103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8492896388436869802690197 398104518207978272001103)
                  ·
                    rfl

theorem cell21_1744438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_1744438 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1744438 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1744438 prefixEnd_1744438 := by exact prefixLift 1744438
  have htrace : WordTrace (prefixWord ++ tailWord_1744438) baseStart_1744438 baseEnd_1744438 := by
    simpa [prefixWord, tailWord_1744438, baseEnd_1744438] using wordTrace_append hprefix tailTrace_1744438
  have hstable : (prefixWord ++ tailWord_1744438).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744438).length < 2 ^ (prefixWord ++ tailWord_1744438).sum := by decide
  have hdescent : baseEnd_1744438 < baseStart_1744438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744466 : List Nat := [3, 2, 2, 1, 2, 2, 2, 2, 5]
def baseStart_1744466 : Nat := 118140960795 + 1744466 * 2 ^ 59
def prefixEnd_1744466 : Nat := 4983230072969 + 3 ^ 40 * 1744466 * 2
def baseEnd_1744466 : Nat := 398110908189456445534379

theorem tailTrace_1744466 : CollatzResearch.WordTrace tailWord_1744466 prefixEnd_1744466 398110908189456445534379 := by
  unfold tailWord_1744466
  simp only [CollatzResearch.WordTrace]
  refine ⟨15906475524526271979601313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42417268065403391945603501 15906475524526271979601313)
  ·
    refine ⟨11929856643394703984700985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15906475524526271979601313 11929856643394703984700985)
    ·
      refine ⟨8947392482546027988525739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11929856643394703984700985 8947392482546027988525739)
      ·
        refine ⟨13421088723819041982788609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8947392482546027988525739 13421088723819041982788609)
        ·
          refine ⟨10065816542864281487091457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13421088723819041982788609 10065816542864281487091457)
          ·
            refine ⟨7549362407148211115318593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10065816542864281487091457 7549362407148211115318593)
            ·
              refine ⟨5662021805361158336488945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7549362407148211115318593 5662021805361158336488945)
              ·
                refine ⟨4246516354020868752366709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5662021805361158336488945 4246516354020868752366709)
                ·
                  refine ⟨398110908189456445534379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4246516354020868752366709 398110908189456445534379)
                  ·
                    rfl

theorem cell21_1744466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_1744466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1744466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1744466 prefixEnd_1744466 := by exact prefixLift 1744466
  have htrace : WordTrace (prefixWord ++ tailWord_1744466) baseStart_1744466 baseEnd_1744466 := by
    simpa [prefixWord, tailWord_1744466, baseEnd_1744466] using wordTrace_append hprefix tailTrace_1744466
  have hstable : (prefixWord ++ tailWord_1744466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744466).length < 2 ^ (prefixWord ++ tailWord_1744466).sum := by decide
  have hdescent : baseEnd_1744466 < baseStart_1744466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744483 : List Nat := [1, 1, 1, 5, 1, 3, 3, 3, 3]
def baseStart_1744483 : Nat := 118140960795 + 1744483 * 2 ^ 59
def prefixEnd_1744483 : Nat := 4983230072969 + 3 ^ 40 * 1744483 * 2
def baseEnd_1744483 : Nat := 398114787821068193751011

theorem tailTrace_1744483 : CollatzResearch.WordTrace tailWord_1744483 prefixEnd_1744483 398114787821068193751011 := by
  unfold tailWord_1744483
  simp only [CollatzResearch.WordTrace]
  refine ⟨63626522139043499821774103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42417681426028999881182735 63626522139043499821774103)
  ·
    refine ⟨95439783208565249732661155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63626522139043499821774103 95439783208565249732661155)
    ·
      refine ⟨143159674812847874598991733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95439783208565249732661155 143159674812847874598991733)
      ·
        refine ⟨13421219513704488243655475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 143159674812847874598991733 13421219513704488243655475)
        ·
          refine ⟨20131829270556732365483213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13421219513704488243655475 20131829270556732365483213)
          ·
            refine ⟨7549435976458774637056205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20131829270556732365483213 7549435976458774637056205)
            ·
              refine ⟨2831038491172040488896077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7549435976458774637056205 2831038491172040488896077)
              ·
                refine ⟨1061639434189515183336029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2831038491172040488896077 1061639434189515183336029)
                ·
                  refine ⟨398114787821068193751011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1061639434189515183336029 398114787821068193751011)
                  ·
                    rfl

theorem cell21_1744483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 3, 3].length) (baseStart_1744483 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1744483 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1744483 prefixEnd_1744483 := by exact prefixLift 1744483
  have htrace : WordTrace (prefixWord ++ tailWord_1744483) baseStart_1744483 baseEnd_1744483 := by
    simpa [prefixWord, tailWord_1744483, baseEnd_1744483] using wordTrace_append hprefix tailTrace_1744483
  have hstable : (prefixWord ++ tailWord_1744483).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744483).length < 2 ^ (prefixWord ++ tailWord_1744483).sum := by decide
  have hdescent : baseEnd_1744483 < baseStart_1744483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744604 : List Nat := [2, 2, 5, 1, 2, 1, 8]
def baseStart_1744604 : Nat := 118140960795 + 1744604 * 2 ^ 59
def prefixEnd_1744604 : Nat := 4983230072969 + 3 ^ 40 * 1744604 * 2
def baseEnd_1744604 : Nat := 44238044629955430248233

theorem tailTrace_1744604 : CollatzResearch.WordTrace tailWord_1744604 prefixEnd_1744604 44238044629955430248233 := by
  unfold tailWord_1744604
  simp only [CollatzResearch.WordTrace]
  refine ⟨31815467685802568743464433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42420623581070091657952577 31815467685802568743464433)
  ·
    refine ⟨23861600764351926557598325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31815467685802568743464433 23861600764351926557598325)
    ·
      refine ⟨2237025071657993114774843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23861600764351926557598325 2237025071657993114774843)
      ·
        refine ⟨3355537607486989672162265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2237025071657993114774843 3355537607486989672162265)
        ·
          refine ⟨2516653205615242254121699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3355537607486989672162265 2516653205615242254121699)
          ·
            refine ⟨3774979808422863381182549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2516653205615242254121699 3774979808422863381182549)
            ·
              refine ⟨44238044629955430248233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3774979808422863381182549 44238044629955430248233)
              ·
                rfl

theorem cell21_1744604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 8].length) (baseStart_1744604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1744604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1744604 prefixEnd_1744604 := by exact prefixLift 1744604
  have htrace : WordTrace (prefixWord ++ tailWord_1744604) baseStart_1744604 baseEnd_1744604 := by
    simpa [prefixWord, tailWord_1744604, baseEnd_1744604] using wordTrace_append hprefix tailTrace_1744604
  have hstable : (prefixWord ++ tailWord_1744604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744604).length < 2 ^ (prefixWord ++ tailWord_1744604).sum := by decide
  have hdescent : baseEnd_1744604 < baseStart_1744604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744638 : List Nat := [4, 2, 2, 1, 4, 1, 2, 5]
def baseStart_1744638 : Nat := 118140960795 + 1744638 * 2 ^ 59
def prefixEnd_1744638 : Nat := 4983230072969 + 3 ^ 40 * 1744638 * 2
def baseEnd_1744638 : Nat := 132716720310940789555787

theorem tailTrace_1744638 : CollatzResearch.WordTrace tailWord_1744638 prefixEnd_1744638 132716720310940789555787 := by
  unfold tailWord_1744638
  simp only [CollatzResearch.WordTrace]
  refine ⟨7954021931685245161708321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42421450302321307529111045 7954021931685245161708321)
  ·
    refine ⟨5965516448763933871281241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7954021931685245161708321 5965516448763933871281241)
    ·
      refine ⟨4474137336572950403460931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5965516448763933871281241 4474137336572950403460931)
      ·
        refine ⟨6711206004859425605191397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4474137336572950403460931 6711206004859425605191397)
        ·
          refine ⟨1258351125911142300973387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6711206004859425605191397 1258351125911142300973387)
          ·
            refine ⟨1887526688866713451460081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1258351125911142300973387 1887526688866713451460081)
            ·
              refine ⟨1415645016650035088595061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1887526688866713451460081 1415645016650035088595061)
              ·
                refine ⟨132716720310940789555787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1415645016650035088595061 132716720310940789555787)
                ·
                  rfl

theorem cell21_1744638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 5].length) (baseStart_1744638 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1744638 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1744638 prefixEnd_1744638 := by exact prefixLift 1744638
  have htrace : WordTrace (prefixWord ++ tailWord_1744638) baseStart_1744638 baseEnd_1744638 := by
    simpa [prefixWord, tailWord_1744638, baseEnd_1744638] using wordTrace_append hprefix tailTrace_1744638
  have hstable : (prefixWord ++ tailWord_1744638).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744638).length < 2 ^ (prefixWord ++ tailWord_1744638).sum := by decide
  have hdescent : baseEnd_1744638 < baseStart_1744638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744663 : List Nat := [1, 1, 3, 4, 2, 3, 7]
def baseStart_1744663 : Nat := 118140960795 + 1744663 * 2 ^ 59
def prefixEnd_1744663 : Nat := 4983230072969 + 3 ^ 40 * 1744663 * 2
def baseEnd_1744663 : Nat := 44239540697047542305627

theorem tailTrace_1744663 : CollatzResearch.WordTrace tailWord_1744663 prefixEnd_1744663 44239540697047542305627 := by
  unfold tailWord_1744663
  simp only [CollatzResearch.WordTrace]
  refine ⟨63633087278391390563326643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42422058185594260375551095 63633087278391390563326643)
  ·
    refine ⟨95449630917587085844989965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63633087278391390563326643 95449630917587085844989965)
    ·
      refine ⟨35793611594095157191871237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95449630917587085844989965 35793611594095157191871237)
      ·
        refine ⟨6711302173892841973475857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35793611594095157191871237 6711302173892841973475857)
        ·
          refine ⟨5033476630419631480106893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6711302173892841973475857 5033476630419631480106893)
          ·
            refine ⟨1887553736407361805040085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5033476630419631480106893 1887553736407361805040085)
            ·
              refine ⟨44239540697047542305627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1887553736407361805040085 44239540697047542305627)
              ·
                rfl

theorem cell21_1744663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 7].length) (baseStart_1744663 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1744663 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1744663 prefixEnd_1744663 := by exact prefixLift 1744663
  have htrace : WordTrace (prefixWord ++ tailWord_1744663) baseStart_1744663 baseEnd_1744663 := by
    simpa [prefixWord, tailWord_1744663, baseEnd_1744663] using wordTrace_append hprefix tailTrace_1744663
  have hstable : (prefixWord ++ tailWord_1744663).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744663).length < 2 ^ (prefixWord ++ tailWord_1744663).sum := by decide
  have hdescent : baseEnd_1744663 < baseStart_1744663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744722 : List Nat := [3, 2, 2, 1, 1, 12]
def baseStart_1744722 : Nat := 118140960795 + 1744722 * 2 ^ 59
def prefixEnd_1744722 : Nat := 4983230072969 + 3 ^ 40 * 1744722 * 2
def baseEnd_1744722 : Nat := 14747012254713218121007

theorem tailTrace_1744722 : CollatzResearch.WordTrace tailWord_1744722 prefixEnd_1744722 14747012254713218121007 := by
  unfold tailWord_1744722
  simp only [CollatzResearch.WordTrace]
  refine ⟨15908809796294410909931105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42423492790118429093149613 15908809796294410909931105)
  ·
    refine ⟨11931607347220808182448329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15908809796294410909931105 11931607347220808182448329)
    ·
      refine ⟨8948705510415606136836247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11931607347220808182448329 8948705510415606136836247)
      ·
        refine ⟨13423058265623409205254371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8948705510415606136836247 13423058265623409205254371)
        ·
          refine ⟨20134587398435113807881557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13423058265623409205254371 20134587398435113807881557)
          ·
            refine ⟨14747012254713218121007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 20134587398435113807881557 14747012254713218121007)
            ·
              rfl

theorem cell21_1744722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 12].length) (baseStart_1744722 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1744722 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1744722 prefixEnd_1744722 := by exact prefixLift 1744722
  have htrace : WordTrace (prefixWord ++ tailWord_1744722) baseStart_1744722 baseEnd_1744722 := by
    simpa [prefixWord, tailWord_1744722, baseEnd_1744722] using wordTrace_append hprefix tailTrace_1744722
  have hstable : (prefixWord ++ tailWord_1744722).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744722).length < 2 ^ (prefixWord ++ tailWord_1744722).sum := by decide
  have hdescent : baseEnd_1744722 < baseStart_1744722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744725 : List Nat := [1, 3, 2, 2, 2, 3, 2, 2, 4]
def baseStart_1744725 : Nat := 118140960795 + 1744725 * 2 ^ 59
def prefixEnd_1744725 : Nat := 4983230072969 + 3 ^ 40 * 1744725 * 2
def baseEnd_1744725 : Nat := 398170015518129550717183

theorem tailTrace_1744725 : CollatzResearch.WordTrace tailWord_1744725 prefixEnd_1744725 398170015518129550717183 := by
  unfold tailWord_1744725
  simp only [CollatzResearch.WordTrace]
  refine ⟨63635348604166775152083629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42423565736111183434722419 63635348604166775152083629)
  ·
    refine ⟨23863255726562540682031361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63635348604166775152083629 23863255726562540682031361)
    ·
      refine ⟨17897441794921905511523521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23863255726562540682031361 17897441794921905511523521)
      ·
        refine ⟨13423081346191429133642641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17897441794921905511523521 13423081346191429133642641)
        ·
          refine ⟨10067311009643571850231981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13423081346191429133642641 10067311009643571850231981)
          ·
            refine ⟨3775241628616339443836993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10067311009643571850231981 3775241628616339443836993)
            ·
              refine ⟨2831431221462254582877745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3775241628616339443836993 2831431221462254582877745)
              ·
                refine ⟨2123573416096690937158309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2831431221462254582877745 2123573416096690937158309)
                ·
                  refine ⟨398170015518129550717183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2123573416096690937158309 398170015518129550717183)
                  ·
                    rfl

theorem cell21_1744725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 2, 4].length) (baseStart_1744725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1744725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1744725 prefixEnd_1744725 := by exact prefixLift 1744725
  have htrace : WordTrace (prefixWord ++ tailWord_1744725) baseStart_1744725 baseEnd_1744725 := by
    simpa [prefixWord, tailWord_1744725, baseEnd_1744725] using wordTrace_append hprefix tailTrace_1744725
  have hstable : (prefixWord ++ tailWord_1744725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744725).length < 2 ^ (prefixWord ++ tailWord_1744725).sum := by decide
  have hdescent : baseEnd_1744725 < baseStart_1744725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744753 : List Nat := [1, 2, 2, 2, 1, 3, 3, 2, 5]
def baseStart_1744753 : Nat := 118140960795 + 1744753 * 2 ^ 59
def prefixEnd_1744753 : Nat := 4983230072969 + 3 ^ 40 * 1744753 * 2
def baseEnd_1744753 : Nat := 398176405499607724250459

theorem tailTrace_1744753 : CollatzResearch.WordTrace tailWord_1744753 prefixEnd_1744753 398176405499607724250459 := by
  unfold tailWord_1744753
  simp only [CollatzResearch.WordTrace]
  refine ⟨63636369848065335934102913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42424246565376890622735275 63636369848065335934102913)
  ·
    refine ⟨47727277386049001950577185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63636369848065335934102913 47727277386049001950577185)
    ·
      refine ⟨35795458039536751462932889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47727277386049001950577185 35795458039536751462932889)
      ·
        refine ⟨26846593529652563597199667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35795458039536751462932889 26846593529652563597199667)
        ·
          refine ⟨40269890294478845395799501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26846593529652563597199667 40269890294478845395799501)
          ·
            refine ⟨15101208860429567023424813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40269890294478845395799501 15101208860429567023424813)
            ·
              refine ⟨5662953322661087633784305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15101208860429567023424813 5662953322661087633784305)
              ·
                refine ⟨4247214991995815725338229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5662953322661087633784305 4247214991995815725338229)
                ·
                  refine ⟨398176405499607724250459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4247214991995815725338229 398176405499607724250459)
                  ·
                    rfl

theorem cell21_1744753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 5].length) (baseStart_1744753 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1744753 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1744753 prefixEnd_1744753 := by exact prefixLift 1744753
  have htrace : WordTrace (prefixWord ++ tailWord_1744753) baseStart_1744753 baseEnd_1744753 := by
    simpa [prefixWord, tailWord_1744753, baseEnd_1744753] using wordTrace_append hprefix tailTrace_1744753
  have hstable : (prefixWord ++ tailWord_1744753).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744753).length < 2 ^ (prefixWord ++ tailWord_1744753).sum := by decide
  have hdescent : baseEnd_1744753 < baseStart_1744753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744767 : List Nat := [1, 1, 2, 2, 1, 1, 3, 4, 6]
def baseStart_1744767 : Nat := 118140960795 + 1744767 * 2 ^ 59
def prefixEnd_1744767 : Nat := 4983230072969 + 3 ^ 40 * 1744767 * 2
def baseEnd_1744767 : Nat := 398179600490346811017097

theorem tailTrace_1744767 : CollatzResearch.WordTrace tailWord_1744767 prefixEnd_1744767 398179600490346811017097 := by
  unfold tailWord_1744767
  simp only [CollatzResearch.WordTrace]
  refine ⟨63636880470014616325112555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42424586980009744216741703 63636880470014616325112555)
  ·
    refine ⟨95455320705021924487668833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63636880470014616325112555 95455320705021924487668833)
    ·
      refine ⟨71591490528766443365751625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95455320705021924487668833 71591490528766443365751625)
      ·
        refine ⟨53693617896574832524313719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71591490528766443365751625 53693617896574832524313719)
        ·
          refine ⟨80540426844862248786470579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53693617896574832524313719 80540426844862248786470579)
          ·
            refine ⟨120810640267293373179705869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80540426844862248786470579 120810640267293373179705869)
            ·
              refine ⟨45303990100235014942389701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120810640267293373179705869 45303990100235014942389701)
              ·
                refine ⟨8494498143794065301698069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45303990100235014942389701 8494498143794065301698069)
                ·
                  refine ⟨398179600490346811017097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8494498143794065301698069 398179600490346811017097)
                  ·
                    rfl

theorem cell21_1744767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 6].length) (baseStart_1744767 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1744767 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1744767 prefixEnd_1744767 := by exact prefixLift 1744767
  have htrace : WordTrace (prefixWord ++ tailWord_1744767) baseStart_1744767 baseEnd_1744767 := by
    simpa [prefixWord, tailWord_1744767, baseEnd_1744767] using wordTrace_append hprefix tailTrace_1744767
  have hstable : (prefixWord ++ tailWord_1744767).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744767).length < 2 ^ (prefixWord ++ tailWord_1744767).sum := by decide
  have hdescent : baseEnd_1744767 < baseStart_1744767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744843 : List Nat := [1, 1, 1, 1, 3, 4, 1, 3, 6]
def baseStart_1744843 : Nat := 118140960795 + 1744843 * 2 ^ 59
def prefixEnd_1744843 : Nat := 4983230072969 + 3 ^ 40 * 1744843 * 2
def baseEnd_1744843 : Nat := 398196944725787567750275

theorem tailTrace_1744843 : CollatzResearch.WordTrace tailWord_1744843 prefixEnd_1744843 398196944725787567750275 := by
  unfold tailWord_1744843
  simp only [CollatzResearch.WordTrace]
  refine ⟨63639652417739281304879183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42426434945159520869919455 63639652417739281304879183)
  ·
    refine ⟨95459478626608921957318775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63639652417739281304879183 95459478626608921957318775)
    ·
      refine ⟨143189217939913382935978163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95459478626608921957318775 143189217939913382935978163)
      ·
        refine ⟨214783826909870074403967245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143189217939913382935978163 214783826909870074403967245)
        ·
          refine ⟨80543935091201277901487717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214783826909870074403967245 80543935091201277901487717)
          ·
            refine ⟨15101987829600239606528947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80543935091201277901487717 15101987829600239606528947)
            ·
              refine ⟨22652981744400359409793421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15101987829600239606528947 22652981744400359409793421)
              ·
                refine ⟨8494868154150134778672533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22652981744400359409793421 8494868154150134778672533)
                ·
                  refine ⟨398196944725787567750275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8494868154150134778672533 398196944725787567750275)
                  ·
                    rfl

theorem cell21_1744843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 6].length) (baseStart_1744843 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1744843 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1744843 prefixEnd_1744843 := by exact prefixLift 1744843
  have htrace : WordTrace (prefixWord ++ tailWord_1744843) baseStart_1744843 baseEnd_1744843 := by
    simpa [prefixWord, tailWord_1744843, baseEnd_1744843] using wordTrace_append hprefix tailTrace_1744843
  have hstable : (prefixWord ++ tailWord_1744843).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744843).length < 2 ^ (prefixWord ++ tailWord_1744843).sum := by decide
  have hdescent : baseEnd_1744843 < baseStart_1744843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744874 : List Nat := [3, 1, 3, 1, 2, 1, 1, 9]
def baseStart_1744874 : Nat := 118140960795 + 1744874 * 2 ^ 59
def prefixEnd_1744874 : Nat := 4983230072969 + 3 ^ 40 * 1744874 * 2
def baseEnd_1744874 : Nat := 132734673116046134244515

theorem tailTrace_1744874 : CollatzResearch.WordTrace tailWord_1744874 prefixEnd_1744874 132734673116046134244515 := by
  unfold tailWord_1744874
  simp only [CollatzResearch.WordTrace]
  refine ⟨15910195770156743399814419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42427188720417982399505117 15910195770156743399814419)
  ·
    refine ⟨23865293655235115099721629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15910195770156743399814419 23865293655235115099721629)
    ·
      refine ⟨8949485120713168162395611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23865293655235115099721629 8949485120713168162395611)
      ·
        refine ⟨13424227681069752243593417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8949485120713168162395611 13424227681069752243593417)
        ·
          refine ⟨10068170760802314182695063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13424227681069752243593417 10068170760802314182695063)
          ·
            refine ⟨15102256141203471274042595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10068170760802314182695063 15102256141203471274042595)
            ·
              refine ⟨22653384211805206911063893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15102256141203471274042595 22653384211805206911063893)
              ·
                refine ⟨132734673116046134244515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22653384211805206911063893 132734673116046134244515)
                ·
                  rfl

theorem cell21_1744874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 9].length) (baseStart_1744874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1744874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1744874 prefixEnd_1744874 := by exact prefixLift 1744874
  have htrace : WordTrace (prefixWord ++ tailWord_1744874) baseStart_1744874 baseEnd_1744874 := by
    simpa [prefixWord, tailWord_1744874, baseEnd_1744874] using wordTrace_append hprefix tailTrace_1744874
  have hstable : (prefixWord ++ tailWord_1744874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744874).length < 2 ^ (prefixWord ++ tailWord_1744874).sum := by decide
  have hdescent : baseEnd_1744874 < baseStart_1744874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744894 : List Nat := [4, 2, 2, 2, 1, 2, 2, 2, 4]
def baseStart_1744894 : Nat := 118140960795 + 1744894 * 2 ^ 59
def prefixEnd_1744894 : Nat := 4983230072969 + 3 ^ 40 * 1744894 * 2
def baseEnd_1744894 : Nat := 398208583620622812400171

theorem tailTrace_1744894 : CollatzResearch.WordTrace tailWord_1744894 prefixEnd_1744894 398208583620622812400171 := by
  unfold tailWord_1744894
  simp only [CollatzResearch.WordTrace]
  refine ⟨7955189067569314626873217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42427675027036344676657157 7955189067569314626873217)
  ·
    refine ⟨5966391800676985970154913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7955189067569314626873217 5966391800676985970154913)
    ·
      refine ⟨4474793850507739477616185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5966391800676985970154913 4474793850507739477616185)
      ·
        refine ⟨3356095387880804608212139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4474793850507739477616185 3356095387880804608212139)
        ·
          refine ⟨5034143081821206912318209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3356095387880804608212139 5034143081821206912318209)
          ·
            refine ⟨3775607311365905184238657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5034143081821206912318209 3775607311365905184238657)
            ·
              refine ⟨2831705483524428888178993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3775607311365905184238657 2831705483524428888178993)
              ·
                refine ⟨2123779112643321666134245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2831705483524428888178993 2123779112643321666134245)
                ·
                  refine ⟨398208583620622812400171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2123779112643321666134245 398208583620622812400171)
                  ·
                    rfl

theorem cell21_1744894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_1744894 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1744894 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1744894 prefixEnd_1744894 := by exact prefixLift 1744894
  have htrace : WordTrace (prefixWord ++ tailWord_1744894) baseStart_1744894 baseEnd_1744894 := by
    simpa [prefixWord, tailWord_1744894, baseEnd_1744894] using wordTrace_append hprefix tailTrace_1744894
  have hstable : (prefixWord ++ tailWord_1744894).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744894).length < 2 ^ (prefixWord ++ tailWord_1744894).sum := by decide
  have hdescent : baseEnd_1744894 < baseStart_1744894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744981 : List Nat := [1, 3, 2, 2, 1, 3, 2, 2, 5]
def baseStart_1744981 : Nat := 118140960795 + 1744981 * 2 ^ 59
def prefixEnd_1744981 : Nat := 4983230072969 + 3 ^ 40 * 1744981 * 2
def baseEnd_1744981 : Nat := 398228438205929994449993

theorem tailTrace_1744981 : CollatzResearch.WordTrace tailWord_1744981 prefixEnd_1744981 398228438205929994449993 := by
  unfold tailWord_1744981
  simp only [CollatzResearch.WordTrace]
  refine ⟨63644685691239330873402797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42429790460826220582268531 63644685691239330873402797)
  ·
    refine ⟨23866757134214749077526049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63644685691239330873402797 23866757134214749077526049)
    ·
      refine ⟨17900067850661061808144537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23866757134214749077526049 17900067850661061808144537)
      ·
        refine ⟨13425050887995796356108403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17900067850661061808144537 13425050887995796356108403)
        ·
          refine ⟨20137576331993694534162605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13425050887995796356108403 20137576331993694534162605)
          ·
            refine ⟨7551591124497635450310977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20137576331993694534162605 7551591124497635450310977)
            ·
              refine ⟨5663693343373226587733233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7551591124497635450310977 5663693343373226587733233)
              ·
                refine ⟨4247770007529919940799925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5663693343373226587733233 4247770007529919940799925)
                ·
                  refine ⟨398228438205929994449993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4247770007529919940799925 398228438205929994449993)
                  ·
                    rfl

theorem cell21_1744981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 5].length) (baseStart_1744981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1744981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1744981 prefixEnd_1744981 := by exact prefixLift 1744981
  have htrace : WordTrace (prefixWord ++ tailWord_1744981) baseStart_1744981 baseEnd_1744981 := by
    simpa [prefixWord, tailWord_1744981, baseEnd_1744981] using wordTrace_append hprefix tailTrace_1744981
  have hstable : (prefixWord ++ tailWord_1744981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744981).length < 2 ^ (prefixWord ++ tailWord_1744981).sum := by decide
  have hdescent : baseEnd_1744981 < baseStart_1744981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744990 : List Nat := [4, 4, 1, 1, 2, 2, 1, 3, 3]
def baseStart_1744990 : Nat := 118140960795 + 1744990 * 2 ^ 59
def prefixEnd_1744990 : Nat := 4983230072969 + 3 ^ 40 * 1744990 * 2
def baseEnd_1744990 : Nat := 398230492128547978799975

theorem tailTrace_1744990 : CollatzResearch.WordTrace tailWord_1744990 prefixEnd_1744990 398230492128547978799975 := by
  unfold tailWord_1744990
  simp only [CollatzResearch.WordTrace]
  refine ⟨7955626743525840676310053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42430009298804483606986949 7955626743525840676310053)
  ·
    refine ⟨1491680014411095126808135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7955626743525840676310053 1491680014411095126808135)
    ·
      refine ⟨2237520021616642690212203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1491680014411095126808135 2237520021616642690212203)
      ·
        refine ⟨3356280032424964035318305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2237520021616642690212203 3356280032424964035318305)
        ·
          refine ⟨2517210024318723026488729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3356280032424964035318305 2517210024318723026488729)
          ·
            refine ⟨1887907518239042269866547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2517210024318723026488729 1887907518239042269866547)
            ·
              refine ⟨2831861277358563404799821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1887907518239042269866547 2831861277358563404799821)
              ·
                refine ⟨1061947979009461276799933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2831861277358563404799821 1061947979009461276799933)
                ·
                  refine ⟨398230492128547978799975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1061947979009461276799933 398230492128547978799975)
                  ·
                    rfl

theorem cell21_1744990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_1744990 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1744990 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1744990 prefixEnd_1744990 := by exact prefixLift 1744990
  have htrace : WordTrace (prefixWord ++ tailWord_1744990) baseStart_1744990 baseEnd_1744990 := by
    simpa [prefixWord, tailWord_1744990, baseEnd_1744990] using wordTrace_append hprefix tailTrace_1744990
  have hstable : (prefixWord ++ tailWord_1744990).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744990).length < 2 ^ (prefixWord ++ tailWord_1744990).sum := by decide
  have hdescent : baseEnd_1744990 < baseStart_1744990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1744995 : List Nat := [1, 1, 1, 5, 1, 1, 3, 2, 6]
def baseStart_1744995 : Nat := 118140960795 + 1744995 * 2 ^ 59
def prefixEnd_1744995 : Nat := 4983230072969 + 3 ^ 40 * 1744995 * 2
def baseEnd_1744995 : Nat := 398231633196669081216631

theorem tailTrace_1744995 : CollatzResearch.WordTrace tailWord_1744995 prefixEnd_1744995 398231633196669081216631 := by
  unfold tailWord_1744995
  simp only [CollatzResearch.WordTrace]
  refine ⟨63645196313188611264412439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42430130875459074176274959 63645196313188611264412439)
  ·
    refine ⟨95467794469782916896618659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63645196313188611264412439 95467794469782916896618659)
    ·
      refine ⟨143201691704674375344927989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95467794469782916896618659 143201691704674375344927989)
      ·
        refine ⟨13425158597313222688586999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 143201691704674375344927989 13425158597313222688586999)
        ·
          refine ⟨20137737895969834032880499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13425158597313222688586999 20137737895969834032880499)
          ·
            refine ⟨30206606843954751049320749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20137737895969834032880499 30206606843954751049320749)
            ·
              refine ⟨11327477566483031643495281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30206606843954751049320749 11327477566483031643495281)
              ·
                refine ⟨8495608174862273732621461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11327477566483031643495281 8495608174862273732621461)
                ·
                  refine ⟨398231633196669081216631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8495608174862273732621461 398231633196669081216631)
                  ·
                    rfl

theorem cell21_1744995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 6].length) (baseStart_1744995 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1744995 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1744995 prefixEnd_1744995 := by exact prefixLift 1744995
  have htrace : WordTrace (prefixWord ++ tailWord_1744995) baseStart_1744995 baseEnd_1744995 := by
    simpa [prefixWord, tailWord_1744995, baseEnd_1744995] using wordTrace_append hprefix tailTrace_1744995
  have hstable : (prefixWord ++ tailWord_1744995).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1744995).length < 2 ^ (prefixWord ++ tailWord_1744995).sum := by decide
  have hdescent : baseEnd_1744995 < baseStart_1744995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1744995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745015 : List Nat := [1, 1, 3, 1, 1, 6, 3, 2, 3]
def baseStart_1745015 : Nat := 118140960795 + 1745015 * 2 ^ 59
def prefixEnd_1745015 : Nat := 4983230072969 + 3 ^ 40 * 1745015 * 2
def baseEnd_1745015 : Nat := 398236197469153490883257

theorem tailTrace_1745015 : CollatzResearch.WordTrace tailWord_1745015 prefixEnd_1745015 398236197469153490883257 := by
  unfold tailWord_1745015
  simp only [CollatzResearch.WordTrace]
  refine ⟨63645925773116154680140499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42430617182077436453426999 63645925773116154680140499)
  ·
    refine ⟨95468888659674232020210749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63645925773116154680140499 95468888659674232020210749)
    ·
      refine ⟨35800833247377837007579031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95468888659674232020210749 35800833247377837007579031)
      ·
        refine ⟨53701249871066755511368547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35800833247377837007579031 53701249871066755511368547)
        ·
          refine ⟨80551874806600133267052821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53701249871066755511368547 80551874806600133267052821)
          ·
            refine ⟨3775869131559381246893101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 80551874806600133267052821 3775869131559381246893101)
            ·
              refine ⟨1415950924334767967584913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3775869131559381246893101 1415950924334767967584913)
              ·
                refine ⟨1061963193251075975688685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1415950924334767967584913 1061963193251075975688685)
                ·
                  refine ⟨398236197469153490883257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1061963193251075975688685 398236197469153490883257)
                  ·
                    rfl

theorem cell21_1745015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 2, 3].length) (baseStart_1745015 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1745015 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1745015 prefixEnd_1745015 := by exact prefixLift 1745015
  have htrace : WordTrace (prefixWord ++ tailWord_1745015) baseStart_1745015 baseEnd_1745015 := by
    simpa [prefixWord, tailWord_1745015, baseEnd_1745015] using wordTrace_append hprefix tailTrace_1745015
  have hstable : (prefixWord ++ tailWord_1745015).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745015).length < 2 ^ (prefixWord ++ tailWord_1745015).sum := by decide
  have hdescent : baseEnd_1745015 < baseStart_1745015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745029 : List Nat := [1, 3, 1, 1, 5, 1, 4, 1, 4]
def baseStart_1745029 : Nat := 118140960795 + 1745029 * 2 ^ 59
def prefixEnd_1745029 : Nat := 4983230072969 + 3 ^ 40 * 1745029 * 2
def baseEnd_1745029 : Nat := 398239392459892577649895

theorem tailTrace_1745029 : CollatzResearch.WordTrace tailWord_1745029 prefixEnd_1745029 398239392459892577649895 := by
  unfold tailWord_1745029
  simp only [CollatzResearch.WordTrace]
  refine ⟨63646436395065435071150141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42430957596710290047433427 63646436395065435071150141)
  ·
    refine ⟨23867413648149538151681303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63646436395065435071150141 23867413648149538151681303)
    ·
      refine ⟨35801120472224307227521955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23867413648149538151681303 35801120472224307227521955)
      ·
        refine ⟨53701680708336460841282933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35801120472224307227521955 53701680708336460841282933)
        ·
          refine ⟨5034532566406543203870275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53701680708336460841282933 5034532566406543203870275)
          ·
            refine ⟨7551798849609814805805413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5034532566406543203870275 7551798849609814805805413)
            ·
              refine ⟨1415962284301840276088515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7551798849609814805805413 1415962284301840276088515)
              ·
                refine ⟨2123943426452760414132773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1415962284301840276088515 2123943426452760414132773)
                ·
                  refine ⟨398239392459892577649895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2123943426452760414132773 398239392459892577649895)
                  ·
                    rfl

theorem cell21_1745029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 1, 4].length) (baseStart_1745029 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1745029 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1745029 prefixEnd_1745029 := by exact prefixLift 1745029
  have htrace : WordTrace (prefixWord ++ tailWord_1745029) baseStart_1745029 baseEnd_1745029 := by
    simpa [prefixWord, tailWord_1745029, baseEnd_1745029] using wordTrace_append hprefix tailTrace_1745029
  have hstable : (prefixWord ++ tailWord_1745029).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745029).length < 2 ^ (prefixWord ++ tailWord_1745029).sum := by decide
  have hdescent : baseEnd_1745029 < baseStart_1745029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745040 : List Nat := [2, 1, 1, 1, 1, 1, 6, 1, 7]
def baseStart_1745040 : Nat := 118140960795 + 1745040 * 2 ^ 59
def prefixEnd_1745040 : Nat := 4983230072969 + 3 ^ 40 * 1745040 * 2
def baseEnd_1745040 : Nat := 398241902809759002966539

theorem tailTrace_1745040 : CollatzResearch.WordTrace tailWord_1745040 prefixEnd_1745040 398241902809759002966539 := by
  unfold tailWord_1745040
  simp only [CollatzResearch.WordTrace]
  refine ⟨31823418799012791974900287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42431225065350389299867049 31823418799012791974900287)
  ·
    refine ⟨47735128198519187962350431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31823418799012791974900287 47735128198519187962350431)
    ·
      refine ⟨71602692297778781943525647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47735128198519187962350431 71602692297778781943525647)
      ·
        refine ⟨107404038446668172915288471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71602692297778781943525647 107404038446668172915288471)
        ·
          refine ⟨161106057670002259372932707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107404038446668172915288471 161106057670002259372932707)
          ·
            refine ⟨241659086505003389059399061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161106057670002259372932707 241659086505003389059399061)
            ·
              refine ⟨11327769679922033862159331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 241659086505003389059399061 11327769679922033862159331)
              ·
                refine ⟨16991654519883050793238997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11327769679922033862159331 16991654519883050793238997)
                ·
                  refine ⟨398241902809759002966539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16991654519883050793238997 398241902809759002966539)
                  ·
                    rfl

theorem cell21_1745040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 7].length) (baseStart_1745040 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1745040 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1745040 prefixEnd_1745040 := by exact prefixLift 1745040
  have htrace : WordTrace (prefixWord ++ tailWord_1745040) baseStart_1745040 baseEnd_1745040 := by
    simpa [prefixWord, tailWord_1745040, baseEnd_1745040] using wordTrace_append hprefix tailTrace_1745040
  have hstable : (prefixWord ++ tailWord_1745040).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745040).length < 2 ^ (prefixWord ++ tailWord_1745040).sum := by decide
  have hdescent : baseEnd_1745040 < baseStart_1745040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745066 : List Nat := [3, 1, 5, 1, 3, 1, 2, 2, 3]
def baseStart_1745066 : Nat := 118140960795 + 1745066 * 2 ^ 59
def prefixEnd_1745066 : Nat := 4983230072969 + 3 ^ 40 * 1745066 * 2
def baseEnd_1745066 : Nat := 398247836363988735533153

theorem tailTrace_1745066 : CollatzResearch.WordTrace tailWord_1745066 prefixEnd_1745066 398247836363988735533153 := by
  unfold tailWord_1745066
  simp only [CollatzResearch.WordTrace]
  refine ⟨15911946473982847597561763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42431857263954260260164701 15911946473982847597561763)
  ·
    refine ⟨23867919710974271396342645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15911946473982847597561763 23867919710974271396342645)
    ·
      refine ⟨2237617472903837943407123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23867919710974271396342645 2237617472903837943407123)
      ·
        refine ⟨3356426209355756915110685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2237617472903837943407123 3356426209355756915110685)
        ·
          refine ⟨1258659828508408843166507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3356426209355756915110685 1258659828508408843166507)
          ·
            refine ⟨1887989742762613264749761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1258659828508408843166507 1887989742762613264749761)
            ·
              refine ⟨1415992307071959948562321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1887989742762613264749761 1415992307071959948562321)
              ·
                refine ⟨1061994230303969961421741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1415992307071959948562321 1061994230303969961421741)
                ·
                  refine ⟨398247836363988735533153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1061994230303969961421741 398247836363988735533153)
                  ·
                    rfl

theorem cell21_1745066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 2, 3].length) (baseStart_1745066 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1745066 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1745066 prefixEnd_1745066 := by exact prefixLift 1745066
  have htrace : WordTrace (prefixWord ++ tailWord_1745066) baseStart_1745066 baseEnd_1745066 := by
    simpa [prefixWord, tailWord_1745066, baseEnd_1745066] using wordTrace_append hprefix tailTrace_1745066
  have hstable : (prefixWord ++ tailWord_1745066).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745066).length < 2 ^ (prefixWord ++ tailWord_1745066).sum := by decide
  have hdescent : baseEnd_1745066 < baseStart_1745066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745074 : List Nat := [3, 2, 1, 1, 1, 3, 3, 4, 3]
def baseStart_1745074 : Nat := 118140960795 + 1745074 * 2 ^ 59
def prefixEnd_1745074 : Nat := 4983230072969 + 3 ^ 40 * 1745074 * 2
def baseEnd_1745074 : Nat := 398249662072982499399803

theorem tailTrace_1745074 : CollatzResearch.WordTrace tailWord_1745074 prefixEnd_1745074 398249662072982499399803 := by
  unfold tailWord_1745074
  simp only [CollatzResearch.WordTrace]
  refine ⟨15912019419975601939134569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42432051786601605171025517 15912019419975601939134569)
  ·
    refine ⟨11934014564981701454350927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15912019419975601939134569 11934014564981701454350927)
    ·
      refine ⟨17901021847472552181526391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11934014564981701454350927 17901021847472552181526391)
      ·
        refine ⟨26851532771208828272289587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17901021847472552181526391 26851532771208828272289587)
        ·
          refine ⟨40277299156813242408434381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26851532771208828272289587 40277299156813242408434381)
          ·
            refine ⟨15103987183804965903162893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40277299156813242408434381 15103987183804965903162893)
            ·
              refine ⟨5663995193926862213686085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15103987183804965903162893 5663995193926862213686085)
              ·
                refine ⟨1061999098861286665066141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5663995193926862213686085 1061999098861286665066141)
                ·
                  refine ⟨398249662072982499399803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1061999098861286665066141 398249662072982499399803)
                  ·
                    rfl

theorem cell21_1745074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 4, 3].length) (baseStart_1745074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1745074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1745074 prefixEnd_1745074 := by exact prefixLift 1745074
  have htrace : WordTrace (prefixWord ++ tailWord_1745074) baseStart_1745074 baseEnd_1745074 := by
    simpa [prefixWord, tailWord_1745074, baseEnd_1745074] using wordTrace_append hprefix tailTrace_1745074
  have hstable : (prefixWord ++ tailWord_1745074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745074).length < 2 ^ (prefixWord ++ tailWord_1745074).sum := by decide
  have hdescent : baseEnd_1745074 < baseStart_1745074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745077 : List Nat := [1, 3, 3, 4, 2, 1, 1, 6]
def baseStart_1745077 : Nat := 118140960795 + 1745077 * 2 ^ 59
def prefixEnd_1745077 : Nat := 4983230072969 + 3 ^ 40 * 1745077 * 2
def baseEnd_1745077 : Nat := 132750115571285053616599

theorem tailTrace_1745077 : CollatzResearch.WordTrace tailWord_1745077 prefixEnd_1745077 132750115571285053616599 := by
  unfold tailWord_1745077
  simp only [CollatzResearch.WordTrace]
  refine ⟨63648187098891539268897485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42432124732594359512598323 63648187098891539268897485)
  ·
    refine ⟨23868070162084327225836557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63648187098891539268897485 23868070162084327225836557)
    ·
      refine ⟨8950526310781622709688709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23868070162084327225836557 8950526310781622709688709)
      ·
        refine ⟨1678223683271554258066633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8950526310781622709688709 1678223683271554258066633)
        ·
          refine ⟨1258667762453665693549975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1678223683271554258066633 1258667762453665693549975)
          ·
            refine ⟨1888001643680498540324963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1258667762453665693549975 1888001643680498540324963)
            ·
              refine ⟨2832002465520747810487445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1888001643680498540324963 2832002465520747810487445)
              ·
                refine ⟨132750115571285053616599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2832002465520747810487445 132750115571285053616599)
                ·
                  rfl

theorem cell21_1745077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 6].length) (baseStart_1745077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1745077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1745077 prefixEnd_1745077 := by exact prefixLift 1745077
  have htrace : WordTrace (prefixWord ++ tailWord_1745077) baseStart_1745077 baseEnd_1745077 := by
    simpa [prefixWord, tailWord_1745077, baseEnd_1745077] using wordTrace_append hprefix tailTrace_1745077
  have hstable : (prefixWord ++ tailWord_1745077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745077).length < 2 ^ (prefixWord ++ tailWord_1745077).sum := by decide
  have hdescent : baseEnd_1745077 < baseStart_1745077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745088 : List Nat := [2, 1, 1, 2, 5, 1, 2, 3, 4]
def baseStart_1745088 : Nat := 118140960795 + 1745088 * 2 ^ 59
def prefixEnd_1745088 : Nat := 4983230072969 + 3 ^ 40 * 1745088 * 2
def baseEnd_1745088 : Nat := 398252857063721586166441

theorem tailTrace_1745088 : CollatzResearch.WordTrace tailWord_1745088 prefixEnd_1745088 398252857063721586166441 := by
  unfold tailWord_1745088
  simp only [CollatzResearch.WordTrace]
  refine ⟨31824294150925844073773959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42432392201234458765031945 31824294150925844073773959)
  ·
    refine ⟨47736441226388766110660939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31824294150925844073773959 47736441226388766110660939)
    ·
      refine ⟨71604661839583149165991409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47736441226388766110660939 71604661839583149165991409)
      ·
        refine ⟨53703496379687361874493557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71604661839583149165991409 53703496379687361874493557)
        ·
          refine ⟨5034702785595690175733771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53703496379687361874493557 5034702785595690175733771)
          ·
            refine ⟨7552054178393535263600657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5034702785595690175733771 7552054178393535263600657)
            ·
              refine ⟨5664040633795151447700493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7552054178393535263600657 5664040633795151447700493)
              ·
                refine ⟨2124015237673181792887685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5664040633795151447700493 2124015237673181792887685)
                ·
                  refine ⟨398252857063721586166441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2124015237673181792887685 398252857063721586166441)
                  ·
                    rfl

theorem cell21_1745088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 3, 4].length) (baseStart_1745088 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1745088 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1745088 prefixEnd_1745088 := by exact prefixLift 1745088
  have htrace : WordTrace (prefixWord ++ tailWord_1745088) baseStart_1745088 baseEnd_1745088 := by
    simpa [prefixWord, tailWord_1745088, baseEnd_1745088] using wordTrace_append hprefix tailTrace_1745088
  have hstable : (prefixWord ++ tailWord_1745088).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745088).length < 2 ^ (prefixWord ++ tailWord_1745088).sum := by decide
  have hdescent : baseEnd_1745088 < baseStart_1745088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745198 : List Nat := [4, 1, 3, 3, 1, 1, 1, 3, 4]
def baseStart_1745198 : Nat := 118140960795 + 1745198 * 2 ^ 59
def prefixEnd_1745198 : Nat := 4983230072969 + 3 ^ 40 * 1745198 * 2
def baseEnd_1745198 : Nat := 398277960562385839332883

theorem tailTrace_1745198 : CollatzResearch.WordTrace tailWord_1745198 prefixEnd_1745198 398277960562385839332883 := by
  unfold tailWord_1745198
  simp only [CollatzResearch.WordTrace]
  refine ⟨7956575041431647116756531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42435066887635451289368165 7956575041431647116756531)
  ·
    refine ⟨11934862562147470675134797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7956575041431647116756531 11934862562147470675134797)
    ·
      refine ⟨4475573460805301503175549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11934862562147470675134797 4475573460805301503175549)
      ·
        refine ⟨1678340047801988063690831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4475573460805301503175549 1678340047801988063690831)
        ·
          refine ⟨2517510071702982095536247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1678340047801988063690831 2517510071702982095536247)
          ·
            refine ⟨3776265107554473143304371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2517510071702982095536247 3776265107554473143304371)
            ·
              refine ⟨5664397661331709714956557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3776265107554473143304371 5664397661331709714956557)
              ·
                refine ⟨2124149122999391143108709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5664397661331709714956557 2124149122999391143108709)
                ·
                  refine ⟨398277960562385839332883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2124149122999391143108709 398277960562385839332883)
                  ·
                    rfl

theorem cell21_1745198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_1745198 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1745198 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1745198 prefixEnd_1745198 := by exact prefixLift 1745198
  have htrace : WordTrace (prefixWord ++ tailWord_1745198) baseStart_1745198 baseEnd_1745198 := by
    simpa [prefixWord, tailWord_1745198, baseEnd_1745198] using wordTrace_append hprefix tailTrace_1745198
  have hstable : (prefixWord ++ tailWord_1745198).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745198).length < 2 ^ (prefixWord ++ tailWord_1745198).sum := by decide
  have hdescent : baseEnd_1745198 < baseStart_1745198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745237 : List Nat := [1, 3, 2, 2, 13]
def baseStart_1745237 : Nat := 118140960795 + 1745237 * 2 ^ 59
def prefixEnd_1745237 : Nat := 4983230072969 + 3 ^ 40 * 1745237 * 2
def baseEnd_1745237 : Nat := 4917121739428770841763

theorem tailTrace_1745237 : CollatzResearch.WordTrace tailWord_1745237 prefixEnd_1745237 4917121739428770841763 := by
  unfold tailWord_1745237
  simp only [CollatzResearch.WordTrace]
  refine ⟨63654022778311886594721965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42436015185541257729814643 63654022778311886594721965)
  ·
    refine ⟨23870258541866957473020737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63654022778311886594721965 23870258541866957473020737)
    ·
      refine ⟨17902693906400218104765553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23870258541866957473020737 17902693906400218104765553)
      ·
        refine ⟨13427020429800163578574165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17902693906400218104765553 13427020429800163578574165)
        ·
          refine ⟨4917121739428770841763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 13427020429800163578574165 4917121739428770841763)
          ·
            rfl

theorem cell21_1745237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 13].length) (baseStart_1745237 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1745237 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1745237 prefixEnd_1745237 := by exact prefixLift 1745237
  have htrace : WordTrace (prefixWord ++ tailWord_1745237) baseStart_1745237 baseEnd_1745237 := by
    simpa [prefixWord, tailWord_1745237, baseEnd_1745237] using wordTrace_append hprefix tailTrace_1745237
  have hstable : (prefixWord ++ tailWord_1745237).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745237).length < 2 ^ (prefixWord ++ tailWord_1745237).sum := by decide
  have hdescent : baseEnd_1745237 < baseStart_1745237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745322 : List Nat := [3, 1, 6, 1, 1, 2, 2, 5]
def baseStart_1745322 : Nat := 118140960795 + 1745322 * 2 ^ 59
def prefixEnd_1745322 : Nat := 4983230072969 + 3 ^ 40 * 1745322 * 2
def baseEnd_1745322 : Nat := 132768753017263059755321

theorem tailTrace_1745322 : CollatzResearch.WordTrace tailWord_1745322 prefixEnd_1745322 132768753017263059755321 := by
  unfold tailWord_1745322
  simp only [CollatzResearch.WordTrace]
  refine ⟨15914280745750986527891555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42438081988669297407710813 15914280745750986527891555)
  ·
    refine ⟨23871421118626479791837333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15914280745750986527891555 23871421118626479791837333)
    ·
      refine ⟨1118972864935616240242375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23871421118626479791837333 1118972864935616240242375)
      ·
        refine ⟨1678459297403424360363563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1118972864935616240242375 1678459297403424360363563)
        ·
          refine ⟨2517688946105136540545345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1678459297403424360363563 2517688946105136540545345)
          ·
            refine ⟨1888266709578852405409009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2517688946105136540545345 1888266709578852405409009)
            ·
              refine ⟨1416200032184139304056757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1888266709578852405409009 1416200032184139304056757)
              ·
                refine ⟨132768753017263059755321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1416200032184139304056757 132768753017263059755321)
                ·
                  rfl

theorem cell21_1745322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 5].length) (baseStart_1745322 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1745322 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1745322 prefixEnd_1745322 := by exact prefixLift 1745322
  have htrace : WordTrace (prefixWord ++ tailWord_1745322) baseStart_1745322 baseEnd_1745322 := by
    simpa [prefixWord, tailWord_1745322, baseEnd_1745322] using wordTrace_append hprefix tailTrace_1745322
  have hstable : (prefixWord ++ tailWord_1745322).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745322).length < 2 ^ (prefixWord ++ tailWord_1745322).sum := by decide
  have hdescent : baseEnd_1745322 < baseStart_1745322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745361 : List Nat := [1, 2, 2, 1, 2, 1, 1, 8, 3]
def baseStart_1745361 : Nat := 118140960795 + 1745361 * 2 ^ 59
def prefixEnd_1745361 : Nat := 4983230072969 + 3 ^ 40 * 1745361 * 2
def baseEnd_1745361 : Nat := 398315159383133778115883

theorem tailTrace_1745361 : CollatzResearch.WordTrace tailWord_1745361 prefixEnd_1745361 398315159383133778115883 := by
  unfold tailWord_1745361
  simp only [CollatzResearch.WordTrace]
  refine ⟨63658545429862655772235937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42439030286575103848157291 63658545429862655772235937)
  ·
    refine ⟨47743909072396991829176953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63658545429862655772235937 47743909072396991829176953)
    ·
      refine ⟨35807931804297743871882715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47743909072396991829176953 35807931804297743871882715)
      ·
        refine ⟨53711897706446615807824073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35807931804297743871882715 53711897706446615807824073)
        ·
          refine ⟨40283923279834961855868055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53711897706446615807824073 40283923279834961855868055)
          ·
            refine ⟨60425884919752442783802083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40283923279834961855868055 60425884919752442783802083)
            ·
              refine ⟨90638827379628664175703125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60425884919752442783802083 90638827379628664175703125)
              ·
                refine ⟨1062173758355023408309021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 90638827379628664175703125 1062173758355023408309021)
                ·
                  refine ⟨398315159383133778115883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1062173758355023408309021 398315159383133778115883)
                  ·
                    rfl

theorem cell21_1745361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 8, 3].length) (baseStart_1745361 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1745361 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1745361 prefixEnd_1745361 := by exact prefixLift 1745361
  have htrace : WordTrace (prefixWord ++ tailWord_1745361) baseStart_1745361 baseEnd_1745361 := by
    simpa [prefixWord, tailWord_1745361, baseEnd_1745361] using wordTrace_append hprefix tailTrace_1745361
  have hstable : (prefixWord ++ tailWord_1745361).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745361).length < 2 ^ (prefixWord ++ tailWord_1745361).sum := by decide
  have hdescent : baseEnd_1745361 < baseStart_1745361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745412 : List Nat := [2, 3, 2, 3, 1, 3, 2, 2, 3]
def baseStart_1745412 : Nat := 118140960795 + 1745412 * 2 ^ 59
def prefixEnd_1745412 : Nat := 4983230072969 + 3 ^ 40 * 1745412 * 2
def baseEnd_1745412 : Nat := 398326798277969022765779

theorem tailTrace_1745412 : CollatzResearch.WordTrace tailWord_1745412 prefixEnd_1745412 398326798277969022765779 := by
  unfold tailWord_1745412
  simp only [CollatzResearch.WordTrace]
  refine ⟨31830202776338945741171245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42440270368451927654894993 31830202776338945741171245)
  ·
    refine ⟨11936326041127104652939217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31830202776338945741171245 11936326041127104652939217)
    ·
      refine ⟨8952244530845328489704413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11936326041127104652939217 8952244530845328489704413)
      ·
        refine ⟨3357091699066998183639155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8952244530845328489704413 3357091699066998183639155)
        ·
          refine ⟨5035637548600497275458733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3357091699066998183639155 5035637548600497275458733)
          ·
            refine ⟨1888364080725186478297025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5035637548600497275458733 1888364080725186478297025)
            ·
              refine ⟨1416273060543889858722769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1888364080725186478297025 1416273060543889858722769)
              ·
                refine ⟨1062204795407917394042077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1416273060543889858722769 1062204795407917394042077)
                ·
                  refine ⟨398326798277969022765779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1062204795407917394042077 398326798277969022765779)
                  ·
                    rfl

theorem cell21_1745412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 2, 3].length) (baseStart_1745412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1745412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1745412 prefixEnd_1745412 := by exact prefixLift 1745412
  have htrace : WordTrace (prefixWord ++ tailWord_1745412) baseStart_1745412 baseEnd_1745412 := by
    simpa [prefixWord, tailWord_1745412, baseEnd_1745412] using wordTrace_append hprefix tailTrace_1745412
  have hstable : (prefixWord ++ tailWord_1745412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745412).length < 2 ^ (prefixWord ++ tailWord_1745412).sum := by decide
  have hdescent : baseEnd_1745412 < baseStart_1745412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745437 : List Nat := [1, 4, 2, 2, 1, 3, 1, 2, 5]
def baseStart_1745437 : Nat := 118140960795 + 1745437 * 2 ^ 59
def prefixEnd_1745437 : Nat := 4983230072969 + 3 ^ 40 * 1745437 * 2
def baseEnd_1745437 : Nat := 398332503618574534849061

theorem tailTrace_1745437 : CollatzResearch.WordTrace tailWord_1745437 prefixEnd_1745437 398332503618574534849061 := by
  unfold tailWord_1745437
  simp only [CollatzResearch.WordTrace]
  refine ⟨63661317377587320752002565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42440878251724880501335043 63661317377587320752002565)
  ·
    refine ⟨11936497008297622641000481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63661317377587320752002565 11936497008297622641000481)
    ·
      refine ⟨8952372756223216980750361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11936497008297622641000481 8952372756223216980750361)
      ·
        refine ⟨6714279567167412735562771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8952372756223216980750361 6714279567167412735562771)
        ·
          refine ⟨10071419350751119103344157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6714279567167412735562771 10071419350751119103344157)
          ·
            refine ⟨3776782256531669663754059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10071419350751119103344157 3776782256531669663754059)
            ·
              refine ⟨5665173384797504495631089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3776782256531669663754059 5665173384797504495631089)
              ·
                refine ⟨4248880038598128371723317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5665173384797504495631089 4248880038598128371723317)
                ·
                  refine ⟨398332503618574534849061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4248880038598128371723317 398332503618574534849061)
                  ·
                    rfl

theorem cell21_1745437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_1745437 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1745437 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1745437 prefixEnd_1745437 := by exact prefixLift 1745437
  have htrace : WordTrace (prefixWord ++ tailWord_1745437) baseStart_1745437 baseEnd_1745437 := by
    simpa [prefixWord, tailWord_1745437, baseEnd_1745437] using wordTrace_append hprefix tailTrace_1745437
  have hstable : (prefixWord ++ tailWord_1745437).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745437).length < 2 ^ (prefixWord ++ tailWord_1745437).sum := by decide
  have hdescent : baseEnd_1745437 < baseStart_1745437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745465 : List Nat := [1, 2, 1, 5, 1, 1, 10]
def baseStart_1745465 : Nat := 118140960795 + 1745465 * 2 ^ 59
def prefixEnd_1745465 : Nat := 4983230072969 + 3 ^ 40 * 1745465 * 2
def baseEnd_1745465 : Nat := 44259877066672523153593

theorem tailTrace_1745465 : CollatzResearch.WordTrace tailWord_1745465 prefixEnd_1745465 44259877066672523153593 := by
  unfold tailWord_1745465
  simp only [CollatzResearch.WordTrace]
  refine ⟨63662338621485881534021849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42441559080990587689347899 63662338621485881534021849)
  ·
    refine ⟨47746753966114411150516387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63662338621485881534021849 47746753966114411150516387)
    ·
      refine ⟨71620130949171616725774581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47746753966114411150516387 71620130949171616725774581)
      ·
        refine ⟨6714387276484839068041367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71620130949171616725774581 6714387276484839068041367)
        ·
          refine ⟨10071580914727258602062051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6714387276484839068041367 10071580914727258602062051)
          ·
            refine ⟨15107371372090887903093077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10071580914727258602062051 15107371372090887903093077)
            ·
              refine ⟨44259877066672523153593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15107371372090887903093077 44259877066672523153593)
              ·
                rfl

theorem cell21_1745465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 10].length) (baseStart_1745465 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1745465 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1745465 prefixEnd_1745465 := by exact prefixLift 1745465
  have htrace : WordTrace (prefixWord ++ tailWord_1745465) baseStart_1745465 baseEnd_1745465 := by
    simpa [prefixWord, tailWord_1745465, baseEnd_1745465] using wordTrace_append hprefix tailTrace_1745465
  have hstable : (prefixWord ++ tailWord_1745465).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745465).length < 2 ^ (prefixWord ++ tailWord_1745465).sum := by decide
  have hdescent : baseEnd_1745465 < baseStart_1745465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745468 : List Nat := [2, 2, 2, 2, 3, 1, 3, 2, 4]
def baseStart_1745468 : Nat := 118140960795 + 1745468 * 2 ^ 59
def prefixEnd_1745468 : Nat := 4983230072969 + 3 ^ 40 * 1745468 * 2
def baseEnd_1745468 : Nat := 398339578240925369832331

theorem tailTrace_1745468 : CollatzResearch.WordTrace tailWord_1745468 prefixEnd_1745468 398339578240925369832331 := by
  unfold tailWord_1745468
  simp only [CollatzResearch.WordTrace]
  refine ⟨31831224020237506523190529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42441632026983342030920705 31831224020237506523190529)
  ·
    refine ⟨23873418015178129892392897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31831224020237506523190529 23873418015178129892392897)
    ·
      refine ⟨17905063511383597419294673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23873418015178129892392897 17905063511383597419294673)
      ·
        refine ⟨13428797633537698064471005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17905063511383597419294673 13428797633537698064471005)
        ·
          refine ⟨5035799112576636774176627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13428797633537698064471005 5035799112576636774176627)
          ·
            refine ⟨7553698668864955161264941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5035799112576636774176627 7553698668864955161264941)
            ·
              refine ⟨2832637000824358185474353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7553698668864955161264941 2832637000824358185474353)
              ·
                refine ⟨2124477750618268639105765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2832637000824358185474353 2124477750618268639105765)
                ·
                  refine ⟨398339578240925369832331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2124477750618268639105765 398339578240925369832331)
                  ·
                    rfl

theorem cell21_1745468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 2, 4].length) (baseStart_1745468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1745468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1745468 prefixEnd_1745468 := by exact prefixLift 1745468
  have htrace : WordTrace (prefixWord ++ tailWord_1745468) baseStart_1745468 baseEnd_1745468 := by
    simpa [prefixWord, tailWord_1745468, baseEnd_1745468] using wordTrace_append hprefix tailTrace_1745468
  have hstable : (prefixWord ++ tailWord_1745468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745468).length < 2 ^ (prefixWord ++ tailWord_1745468).sum := by decide
  have hdescent : baseEnd_1745468 < baseStart_1745468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745496 : List Nat := [2, 1, 2, 2, 1, 2, 4, 2, 5]
def baseStart_1745496 : Nat := 118140960795 + 1745496 * 2 ^ 59
def prefixEnd_1745496 : Nat := 4983230072969 + 3 ^ 40 * 1745496 * 2
def baseEnd_1745496 : Nat := 398345968222403543365607

theorem tailTrace_1745496 : CollatzResearch.WordTrace tailWord_1745496 prefixEnd_1745496 398345968222403543365607 := by
  unfold tailWord_1745496
  simp only [CollatzResearch.WordTrace]
  refine ⟨31831734642186786914200171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42442312856249049218933561 31831734642186786914200171)
  ·
    refine ⟨47747601963280180371300257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31831734642186786914200171 47747601963280180371300257)
    ·
      refine ⟨35810701472460135278475193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47747601963280180371300257 35810701472460135278475193)
      ·
        refine ⟨26858026104345101458856395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35810701472460135278475193 26858026104345101458856395)
        ·
          refine ⟨40287039156517652188284593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26858026104345101458856395 40287039156517652188284593)
          ·
            refine ⟨30215279367388239141213445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40287039156517652188284593 30215279367388239141213445)
            ·
              refine ⟨5665364881385294838977521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30215279367388239141213445 5665364881385294838977521)
              ·
                refine ⟨4249023661038971129233141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5665364881385294838977521 4249023661038971129233141)
                ·
                  refine ⟨398345968222403543365607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4249023661038971129233141 398345968222403543365607)
                  ·
                    rfl

theorem cell21_1745496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 5].length) (baseStart_1745496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1745496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1745496 prefixEnd_1745496 := by exact prefixLift 1745496
  have htrace : WordTrace (prefixWord ++ tailWord_1745496) baseStart_1745496 baseEnd_1745496 := by
    simpa [prefixWord, tailWord_1745496, baseEnd_1745496] using wordTrace_append hprefix tailTrace_1745496
  have hstable : (prefixWord ++ tailWord_1745496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745496).length < 2 ^ (prefixWord ++ tailWord_1745496).sum := by decide
  have hdescent : baseEnd_1745496 < baseStart_1745496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745541 : List Nat := [1, 3, 1, 1, 4, 2, 1, 8]
def baseStart_1745541 : Nat := 118140960795 + 1745541 * 2 ^ 59
def prefixEnd_1745541 : Nat := 4983230072969 + 3 ^ 40 * 1745541 * 2
def baseEnd_1745541 : Nat := 132785412611831155038505

theorem tailTrace_1745541 : CollatzResearch.WordTrace tailWord_1745541 prefixEnd_1745541 132785412611831155038505 := by
  unfold tailWord_1745541
  simp only [CollatzResearch.WordTrace]
  refine ⟨63665110569210546513788477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42443407046140364342525651 63665110569210546513788477)
  ·
    refine ⟨23874416463453954942670679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63665110569210546513788477 23874416463453954942670679)
    ·
      refine ⟨35811624695180932414006019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23874416463453954942670679 35811624695180932414006019)
      ·
        refine ⟨53717437042771398621009029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35811624695180932414006019 53717437042771398621009029)
        ·
          refine ⟨10072019445519637241439193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53717437042771398621009029 10072019445519637241439193)
          ·
            refine ⟨7554014584139727931079395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10072019445519637241439193 7554014584139727931079395)
            ·
              refine ⟨11331021876209591896619093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7554014584139727931079395 11331021876209591896619093)
              ·
                refine ⟨132785412611831155038505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11331021876209591896619093 132785412611831155038505)
                ·
                  rfl

theorem cell21_1745541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 8].length) (baseStart_1745541 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1745541 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1745541 prefixEnd_1745541 := by exact prefixLift 1745541
  have htrace : WordTrace (prefixWord ++ tailWord_1745541) baseStart_1745541 baseEnd_1745541 := by
    simpa [prefixWord, tailWord_1745541, baseEnd_1745541] using wordTrace_append hprefix tailTrace_1745541
  have hstable : (prefixWord ++ tailWord_1745541).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745541).length < 2 ^ (prefixWord ++ tailWord_1745541).sum := by decide
  have hdescent : baseEnd_1745541 < baseStart_1745541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745575 : List Nat := [1, 1, 6, 3, 2, 8]
def baseStart_1745575 : Nat := 118140960795 + 1745575 * 2 ^ 59
def prefixEnd_1745575 : Nat := 4983230072969 + 3 ^ 40 * 1745575 * 2
def baseEnd_1745575 : Nat := 14754222114767294872177

theorem tailTrace_1745575 : CollatzResearch.WordTrace tailWord_1745575 prefixEnd_1745575 14754222114767294872177 := by
  unfold tailWord_1745575
  simp only [CollatzResearch.WordTrace]
  refine ⟨63666350651087370320526179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42444233767391580213684119 63666350651087370320526179)
  ·
    refine ⟨95499525976631055480789269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63666350651087370320526179 95499525976631055480789269)
    ·
      refine ⟨4476540280154580725661997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 95499525976631055480789269 4476540280154580725661997)
      ·
        refine ⟨1678702605057967772123249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4476540280154580725661997 1678702605057967772123249)
        ·
          refine ⟨1259026953793475829092437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1678702605057967772123249 1259026953793475829092437)
          ·
            refine ⟨14754222114767294872177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1259026953793475829092437 14754222114767294872177)
            ·
              rfl

theorem cell21_1745575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 8].length) (baseStart_1745575 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1745575 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1745575 prefixEnd_1745575 := by exact prefixLift 1745575
  have htrace : WordTrace (prefixWord ++ tailWord_1745575) baseStart_1745575 baseEnd_1745575 := by
    simpa [prefixWord, tailWord_1745575, baseEnd_1745575] using wordTrace_append hprefix tailTrace_1745575
  have hstable : (prefixWord ++ tailWord_1745575).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745575).length < 2 ^ (prefixWord ++ tailWord_1745575).sum := by decide
  have hdescent : baseEnd_1745575 < baseStart_1745575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745578 : List Nat := [3, 1, 5, 2, 1, 1, 2, 2, 4]
def baseStart_1745578 : Nat := 118140960795 + 1745578 * 2 ^ 59
def prefixEnd_1745578 : Nat := 4983230072969 + 3 ^ 40 * 1745578 * 2
def baseEnd_1745578 : Nat := 398364681739589622998773

theorem tailTrace_1745578 : CollatzResearch.WordTrace tailWord_1745578 prefixEnd_1745578 398364681739589622998773 := by
  unfold tailWord_1745578
  simp only [CollatzResearch.WordTrace]
  refine ⟨15916615017519125458221347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42444306713384334555256925 15916615017519125458221347)
  ·
    refine ⟨23874922526278688187332021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15916615017519125458221347 23874922526278688187332021)
    ·
      refine ⟨2238273986838627017562377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23874922526278688187332021 2238273986838627017562377)
      ·
        refine ⟨1678705490128970263171783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2238273986838627017562377 1678705490128970263171783)
        ·
          refine ⟨2518058235193455394757675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1678705490128970263171783 2518058235193455394757675)
          ·
            refine ⟨3777087352790183092136513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2518058235193455394757675 3777087352790183092136513)
            ·
              refine ⟨2832815514592637319102385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3777087352790183092136513 2832815514592637319102385)
              ·
                refine ⟨2124611635944477989326789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2832815514592637319102385 2124611635944477989326789)
                ·
                  refine ⟨398364681739589622998773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2124611635944477989326789 398364681739589622998773)
                  ·
                    rfl

theorem cell21_1745578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 2, 4].length) (baseStart_1745578 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1745578 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1745578 prefixEnd_1745578 := by exact prefixLift 1745578
  have htrace : WordTrace (prefixWord ++ tailWord_1745578) baseStart_1745578 baseEnd_1745578 := by
    simpa [prefixWord, tailWord_1745578, baseEnd_1745578] using wordTrace_append hprefix tailTrace_1745578
  have hstable : (prefixWord ++ tailWord_1745578).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745578).length < 2 ^ (prefixWord ++ tailWord_1745578).sum := by decide
  have hdescent : baseEnd_1745578 < baseStart_1745578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745648 : List Nat := [2, 1, 1, 1, 3, 1, 6, 1, 5]
def baseStart_1745648 : Nat := 118140960795 + 1745648 * 2 ^ 59
def prefixEnd_1745648 : Nat := 4983230072969 + 3 ^ 40 * 1745648 * 2
def baseEnd_1745648 : Nat := 398380656693285056831963

theorem tailTrace_1745648 : CollatzResearch.WordTrace tailWord_1745648 prefixEnd_1745648 398380656693285056831963 := by
  unfold tailWord_1745648
  simp only [CollatzResearch.WordTrace]
  refine ⟨31834506589911451893966799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42446008786548602525289065 31834506589911451893966799)
  ·
    refine ⟨47751759884867177840950199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31834506589911451893966799 47751759884867177840950199)
    ·
      refine ⟨71627639827300766761425299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47751759884867177840950199 71627639827300766761425299)
      ·
        refine ⟨107441459740951150142137949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71627639827300766761425299 107441459740951150142137949)
        ·
          refine ⟨40290547402856681303301731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107441459740951150142137949 40290547402856681303301731)
          ·
            refine ⟨60435821104285021954952597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40290547402856681303301731 60435821104285021954952597)
            ·
              refine ⟨2832929114263360404138403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 60435821104285021954952597 2832929114263360404138403)
              ·
                refine ⟨4249393671395040606207605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2832929114263360404138403 4249393671395040606207605)
                ·
                  refine ⟨398380656693285056831963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4249393671395040606207605 398380656693285056831963)
                  ·
                    rfl

theorem cell21_1745648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 5].length) (baseStart_1745648 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1745648 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1745648 prefixEnd_1745648 := by exact prefixLift 1745648
  have htrace : WordTrace (prefixWord ++ tailWord_1745648) baseStart_1745648 baseEnd_1745648 := by
    simpa [prefixWord, tailWord_1745648, baseEnd_1745648] using wordTrace_append hprefix tailTrace_1745648
  have hstable : (prefixWord ++ tailWord_1745648).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745648).length < 2 ^ (prefixWord ++ tailWord_1745648).sum := by decide
  have hdescent : baseEnd_1745648 < baseStart_1745648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745710 : List Nat := [4, 1, 3, 2, 1, 1, 1, 8]
def baseStart_1745710 : Nat := 118140960795 + 1745710 * 2 ^ 59
def prefixEnd_1745710 : Nat := 4983230072969 + 3 ^ 40 * 1745710 * 2
def baseEnd_1745710 : Nat := 132798268645995575599501

theorem tailTrace_1745710 : CollatzResearch.WordTrace tailWord_1745710 prefixEnd_1745710 132798268645995575599501 := by
  unfold tailWord_1745710
  simp only [CollatzResearch.WordTrace]
  refine ⟨7958909313199786047086323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42447516337065525584460389 7958909313199786047086323)
  ·
    refine ⟨11938363969799679070629485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7958909313199786047086323 11938363969799679070629485)
    ·
      refine ⟨4476886488674879651486057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11938363969799679070629485 4476886488674879651486057)
      ·
        refine ⟨3357664866506159738614543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4476886488674879651486057 3357664866506159738614543)
        ·
          refine ⟨5036497299759239607921815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3357664866506159738614543 5036497299759239607921815)
          ·
            refine ⟨7554745949638859411882723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5036497299759239607921815 7554745949638859411882723)
            ·
              refine ⟨11332118924458289117824085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7554745949638859411882723 11332118924458289117824085)
              ·
                refine ⟨132798268645995575599501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11332118924458289117824085 132798268645995575599501)
                ·
                  rfl

theorem cell21_1745710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 8].length) (baseStart_1745710 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1745710 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1745710 prefixEnd_1745710 := by exact prefixLift 1745710
  have htrace : WordTrace (prefixWord ++ tailWord_1745710) baseStart_1745710 baseEnd_1745710 := by
    simpa [prefixWord, tailWord_1745710, baseEnd_1745710] using wordTrace_append hprefix tailTrace_1745710
  have hstable : (prefixWord ++ tailWord_1745710).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745710).length < 2 ^ (prefixWord ++ tailWord_1745710).sum := by decide
  have hdescent : baseEnd_1745710 < baseStart_1745710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745738 : List Nat := [3, 1, 2, 1, 1, 1, 2, 4, 6]
def baseStart_1745738 : Nat := 118140960795 + 1745738 * 2 ^ 59
def prefixEnd_1745738 : Nat := 4983230072969 + 3 ^ 40 * 1745738 * 2
def baseEnd_1745738 : Nat := 398401195919464900331779

theorem tailTrace_1745738 : CollatzResearch.WordTrace tailWord_1745738 prefixEnd_1745738 398401195919464900331779 := by
  unfold tailWord_1745738
  simp only [CollatzResearch.WordTrace]
  refine ⟨15918073937374212289677467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42448197166331232772473245 15918073937374212289677467)
  ·
    refine ⟨23877110906061318434516201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15918073937374212289677467 23877110906061318434516201)
    ·
      refine ⟨17907833179545988825887151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23877110906061318434516201 17907833179545988825887151)
      ·
        refine ⟨26861749769318983238830727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17907833179545988825887151 26861749769318983238830727)
        ·
          refine ⟨40292624653978474858246091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26861749769318983238830727 40292624653978474858246091)
          ·
            refine ⟨60438936980967712287369137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40292624653978474858246091 60438936980967712287369137)
            ·
              refine ⟨45329202735725784215526853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60438936980967712287369137 45329202735725784215526853)
              ·
                refine ⟨8499225512948584540411285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45329202735725784215526853 8499225512948584540411285)
                ·
                  refine ⟨398401195919464900331779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8499225512948584540411285 398401195919464900331779)
                  ·
                    rfl

theorem cell21_1745738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 6].length) (baseStart_1745738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1745738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1745738 prefixEnd_1745738 := by exact prefixLift 1745738
  have htrace : WordTrace (prefixWord ++ tailWord_1745738) baseStart_1745738 baseEnd_1745738 := by
    simpa [prefixWord, tailWord_1745738, baseEnd_1745738] using wordTrace_append hprefix tailTrace_1745738
  have hstable : (prefixWord ++ tailWord_1745738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745738).length < 2 ^ (prefixWord ++ tailWord_1745738).sum := by decide
  have hdescent : baseEnd_1745738 < baseStart_1745738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745837 : List Nat := [1, 5, 2, 3, 2, 1, 2, 5]
def baseStart_1745837 : Nat := 118140960795 + 1745837 * 2 ^ 59
def prefixEnd_1745837 : Nat := 4983230072969 + 3 ^ 40 * 1745837 * 2
def baseEnd_1745837 : Nat := 132807929689420909393859

theorem tailTrace_1745837 : CollatzResearch.WordTrace tailWord_1745837 prefixEnd_1745837 132807929689420909393859 := by
  unfold tailWord_1745837
  simp only [CollatzResearch.WordTrace]
  refine ⟨63675906576138189066563765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42450604384092126044375843 63675906576138189066563765)
  ·
    refine ⟨5969616241512955224990353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63675906576138189066563765 5969616241512955224990353)
    ·
      refine ⟨4477212181134716418742765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5969616241512955224990353 4477212181134716418742765)
      ·
        refine ⟨1678954567925518657028537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4477212181134716418742765 1678954567925518657028537)
        ·
          refine ⟨1259215925944138992771403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1678954567925518657028537 1259215925944138992771403)
          ·
            refine ⟨1888823888916208489157105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1259215925944138992771403 1888823888916208489157105)
            ·
              refine ⟨1416617916687156366867829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1888823888916208489157105 1416617916687156366867829)
              ·
                refine ⟨132807929689420909393859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1416617916687156366867829 132807929689420909393859)
                ·
                  rfl

theorem cell21_1745837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 5].length) (baseStart_1745837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1745837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1745837 prefixEnd_1745837 := by exact prefixLift 1745837
  have htrace : WordTrace (prefixWord ++ tailWord_1745837) baseStart_1745837 baseEnd_1745837 := by
    simpa [prefixWord, tailWord_1745837, baseEnd_1745837] using wordTrace_append hprefix tailTrace_1745837
  have hstable : (prefixWord ++ tailWord_1745837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745837).length < 2 ^ (prefixWord ++ tailWord_1745837).sum := by decide
  have hdescent : baseEnd_1745837 < baseStart_1745837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745845 : List Nat := [1, 3, 3, 2, 1, 1, 3, 7]
def baseStart_1745845 : Nat := 118140960795 + 1745845 * 2 ^ 59
def prefixEnd_1745845 : Nat := 4983230072969 + 3 ^ 40 * 1745845 * 2
def baseEnd_1745845 : Nat := 132808538259085497349409

theorem tailTrace_1745845 : CollatzResearch.WordTrace tailWord_1745845 prefixEnd_1745845 132808538259085497349409 := by
  unfold tailWord_1745845
  simp only [CollatzResearch.WordTrace]
  refine ⟨63676198360109206432854989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42450798906739470955236659 63676198360109206432854989)
  ·
    refine ⟨23878574385040952412320621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63676198360109206432854989 23878574385040952412320621)
    ·
      refine ⟨8954465394390357154620233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23878574385040952412320621 8954465394390357154620233)
      ·
        refine ⟨6715849045792767865965175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8954465394390357154620233 6715849045792767865965175)
        ·
          refine ⟨10073773568689151798947763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6715849045792767865965175 10073773568689151798947763)
          ·
            refine ⟨15110660353033727698421645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10073773568689151798947763 15110660353033727698421645)
            ·
              refine ⟨5666497632387647886908117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15110660353033727698421645 5666497632387647886908117)
              ·
                refine ⟨132808538259085497349409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5666497632387647886908117 132808538259085497349409)
                ·
                  rfl

theorem cell21_1745845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 7].length) (baseStart_1745845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1745845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1745845 prefixEnd_1745845 := by exact prefixLift 1745845
  have htrace : WordTrace (prefixWord ++ tailWord_1745845) baseStart_1745845 baseEnd_1745845 := by
    simpa [prefixWord, tailWord_1745845, baseEnd_1745845] using wordTrace_append hprefix tailTrace_1745845
  have hstable : (prefixWord ++ tailWord_1745845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745845).length < 2 ^ (prefixWord ++ tailWord_1745845).sum := by decide
  have hdescent : baseEnd_1745845 < baseStart_1745845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1745969 : List Nat := [1, 2, 2, 3, 1, 2, 4, 3, 3]
def baseStart_1745969 : Nat := 118140960795 + 1745969 * 2 ^ 59
def prefixEnd_1745969 : Nat := 4983230072969 + 3 ^ 40 * 1745969 * 2
def baseEnd_1745969 : Nat := 398453913266659831981307

theorem tailTrace_1745969 : CollatzResearch.WordTrace tailWord_1745969 prefixEnd_1745969 398453913266659831981307 := by
  unfold tailWord_1745969
  simp only [CollatzResearch.WordTrace]
  refine ⟨63680721011659975610368961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42453814007773317073579307 63680721011659975610368961)
  ·
    refine ⟨47760540758744981707776721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63680721011659975610368961 47760540758744981707776721)
    ·
      refine ⟨35820405569058736280832541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47760540758744981707776721 35820405569058736280832541)
      ·
        refine ⟨13432652088397026105312203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35820405569058736280832541 13432652088397026105312203)
        ·
          refine ⟨20148978132595539157968305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13432652088397026105312203 20148978132595539157968305)
          ·
            refine ⟨15111733599446654368476229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20148978132595539157968305 15111733599446654368476229)
            ·
              refine ⟨2833450049896247694089293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15111733599446654368476229 2833450049896247694089293)
              ·
                refine ⟨1062543768711092885283485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2833450049896247694089293 1062543768711092885283485)
                ·
                  refine ⟨398453913266659831981307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1062543768711092885283485 398453913266659831981307)
                  ·
                    rfl

theorem cell21_1745969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 3, 3].length) (baseStart_1745969 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1745969 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1745969 prefixEnd_1745969 := by exact prefixLift 1745969
  have htrace : WordTrace (prefixWord ++ tailWord_1745969) baseStart_1745969 baseEnd_1745969 := by
    simpa [prefixWord, tailWord_1745969, baseEnd_1745969] using wordTrace_append hprefix tailTrace_1745969
  have hstable : (prefixWord ++ tailWord_1745969).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1745969).length < 2 ^ (prefixWord ++ tailWord_1745969).sum := by decide
  have hdescent : baseEnd_1745969 < baseStart_1745969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1745969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746149 : List Nat := [1, 3, 1, 4, 3, 1, 8]
def baseStart_1746149 : Nat := 118140960795 + 1746149 * 2 ^ 59
def prefixEnd_1746149 : Nat := 4983230072969 + 3 ^ 40 * 1746149 * 2
def baseEnd_1746149 : Nat := 44277221302113279886771

theorem tailTrace_1746149 : CollatzResearch.WordTrace tailWord_1746149 prefixEnd_1746149 44277221302113279886771 := by
  unfold tailWord_1746149
  simp only [CollatzResearch.WordTrace]
  refine ⟨63687286151007866351921501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42458190767338577567947667 63687286151007866351921501)
  ·
    refine ⟨23882732306627949881970563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63687286151007866351921501 23882732306627949881970563)
    ·
      refine ⟨35824098459941924822955845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23882732306627949881970563 35824098459941924822955845)
      ·
        refine ⟨6717018461239110904304221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35824098459941924822955845 6717018461239110904304221)
        ·
          refine ⟨2518881922964666589114083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6717018461239110904304221 2518881922964666589114083)
          ·
            refine ⟨3778322884446999883671125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2518881922964666589114083 3778322884446999883671125)
            ·
              refine ⟨44277221302113279886771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3778322884446999883671125 44277221302113279886771)
              ·
                rfl

theorem cell21_1746149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 8].length) (baseStart_1746149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1746149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1746149 prefixEnd_1746149 := by exact prefixLift 1746149
  have htrace : WordTrace (prefixWord ++ tailWord_1746149) baseStart_1746149 baseEnd_1746149 := by
    simpa [prefixWord, tailWord_1746149, baseEnd_1746149] using wordTrace_append hprefix tailTrace_1746149
  have hstable : (prefixWord ++ tailWord_1746149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746149).length < 2 ^ (prefixWord ++ tailWord_1746149).sum := by decide
  have hdescent : baseEnd_1746149 < baseStart_1746149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746163 : List Nat := [1, 1, 1, 2, 2, 5, 1, 3, 5]
def baseStart_1746163 : Nat := 118140960795 + 1746163 * 2 ^ 59
def prefixEnd_1746163 : Nat := 4983230072969 + 3 ^ 40 * 1746163 * 2
def baseEnd_1746163 : Nat := 398498186709758605747577

theorem tailTrace_1746163 : CollatzResearch.WordTrace tailWord_1746163 prefixEnd_1746163 398498186709758605747577 := by
  unfold tailWord_1746163
  simp only [CollatzResearch.WordTrace]
  refine ⟨63687796772957146742931143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42458531181971431161954095 63687796772957146742931143)
  ·
    refine ⟨95531695159435720114396715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63687796772957146742931143 95531695159435720114396715)
    ·
      refine ⟨143297542739153580171595073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95531695159435720114396715 143297542739153580171595073)
      ·
        refine ⟨107473157054365185128696305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143297542739153580171595073 107473157054365185128696305)
        ·
          refine ⟨80604867790773888846522229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107473157054365185128696305 80604867790773888846522229)
          ·
            refine ⟨7556706355385052079361459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80604867790773888846522229 7556706355385052079361459)
            ·
              refine ⟨11335059533077578119042189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7556706355385052079361459 11335059533077578119042189)
              ·
                refine ⟨4250647324904091794640821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11335059533077578119042189 4250647324904091794640821)
                ·
                  refine ⟨398498186709758605747577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4250647324904091794640821 398498186709758605747577)
                  ·
                    rfl

theorem cell21_1746163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 5].length) (baseStart_1746163 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1746163 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1746163 prefixEnd_1746163 := by exact prefixLift 1746163
  have htrace : WordTrace (prefixWord ++ tailWord_1746163) baseStart_1746163 baseEnd_1746163 := by
    simpa [prefixWord, tailWord_1746163, baseEnd_1746163] using wordTrace_append hprefix tailTrace_1746163
  have hstable : (prefixWord ++ tailWord_1746163).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746163).length < 2 ^ (prefixWord ++ tailWord_1746163).sum := by decide
  have hdescent : baseEnd_1746163 < baseStart_1746163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746180 : List Nat := [2, 3, 2, 2, 2, 1, 2, 2, 5]
def baseStart_1746180 : Nat := 118140960795 + 1746180 * 2 ^ 59
def prefixEnd_1746180 : Nat := 4983230072969 + 3 ^ 40 * 1746180 * 2
def baseEnd_1746180 : Nat := 398502066341370353964209

theorem tailTrace_1746180 : CollatzResearch.WordTrace tailWord_1746180 prefixEnd_1746180 398502066341370353964209 := by
  unfold tailWord_1746180
  simp only [CollatzResearch.WordTrace]
  refine ⟨31844208406947779323149997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42458944542597039097533329 31844208406947779323149997)
  ·
    refine ⟨11941578152605417246181249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31844208406947779323149997 11941578152605417246181249)
    ·
      refine ⟨8956183614454062934635937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11941578152605417246181249 8956183614454062934635937)
      ·
        refine ⟨6717137710840547200976953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8956183614454062934635937 6717137710840547200976953)
        ·
          refine ⟨5037853283130410400732715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6717137710840547200976953 5037853283130410400732715)
          ·
            refine ⟨7556779924695615601099073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5037853283130410400732715 7556779924695615601099073)
            ·
              refine ⟨5667584943521711700824305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7556779924695615601099073 5667584943521711700824305)
              ·
                refine ⟨4250688707641283775618229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5667584943521711700824305 4250688707641283775618229)
                ·
                  refine ⟨398502066341370353964209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4250688707641283775618229 398502066341370353964209)
                  ·
                    rfl

theorem cell21_1746180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_1746180 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1746180 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1746180 prefixEnd_1746180 := by exact prefixLift 1746180
  have htrace : WordTrace (prefixWord ++ tailWord_1746180) baseStart_1746180 baseEnd_1746180 := by
    simpa [prefixWord, tailWord_1746180, baseEnd_1746180] using wordTrace_append hprefix tailTrace_1746180
  have hstable : (prefixWord ++ tailWord_1746180).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746180).length < 2 ^ (prefixWord ++ tailWord_1746180).sum := by decide
  have hdescent : baseEnd_1746180 < baseStart_1746180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746225 : List Nat := [1, 2, 2, 3, 3, 2, 2, 6]
def baseStart_1746225 : Nat := 118140960795 + 1746225 * 2 ^ 59
def prefixEnd_1746225 : Nat := 4983230072969 + 3 ^ 40 * 1746225 * 2
def baseEnd_1746225 : Nat := 132837445318153425238039

theorem tailTrace_1746225 : CollatzResearch.WordTrace tailWord_1746225 prefixEnd_1746225 132837445318153425238039 := by
  unfold tailWord_1746225
  simp only [CollatzResearch.WordTrace]
  refine ⟨63690058098732531331688129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42460038732488354221125419 63690058098732531331688129)
  ·
    refine ⟨47767543574049398498766097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63690058098732531331688129 47767543574049398498766097)
    ·
      refine ⟨35825657680537048874074573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47767543574049398498766097 35825657680537048874074573)
      ·
        refine ⟨13434621630201393327777965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35825657680537048874074573 13434621630201393327777965)
        ·
          refine ⟨5037983111325522497916737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13434621630201393327777965 5037983111325522497916737)
          ·
            refine ⟨3778487333494141873437553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5037983111325522497916737 3778487333494141873437553)
            ·
              refine ⟨2833865500120606405078165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3778487333494141873437553 2833865500120606405078165)
              ·
                refine ⟨132837445318153425238039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2833865500120606405078165 132837445318153425238039)
                ·
                  rfl

theorem cell21_1746225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 6].length) (baseStart_1746225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1746225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1746225 prefixEnd_1746225 := by exact prefixLift 1746225
  have htrace : WordTrace (prefixWord ++ tailWord_1746225) baseStart_1746225 baseEnd_1746225 := by
    simpa [prefixWord, tailWord_1746225, baseEnd_1746225] using wordTrace_append hprefix tailTrace_1746225
  have hstable : (prefixWord ++ tailWord_1746225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746225).length < 2 ^ (prefixWord ++ tailWord_1746225).sum := by decide
  have hdescent : baseEnd_1746225 < baseStart_1746225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746256 : List Nat := [2, 1, 1, 1, 1, 5, 2, 5, 3]
def baseStart_1746256 : Nat := 118140960795 + 1746256 * 2 ^ 59
def prefixEnd_1746256 : Nat := 4983230072969 + 3 ^ 40 * 1746256 * 2
def baseEnd_1746256 : Nat := 398519410576811110697387

theorem tailTrace_1746256 : CollatzResearch.WordTrace tailWord_1746256 prefixEnd_1746256 398519410576811110697387 := by
  unfold tailWord_1746256
  simp only [CollatzResearch.WordTrace]
  refine ⟨31845594380810111813033311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42460792507746815750711081 31845594380810111813033311)
  ·
    refine ⟨47768391571215167719549967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31845594380810111813033311 47768391571215167719549967)
    ·
      refine ⟨71652587356822751579324951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47768391571215167719549967 71652587356822751579324951)
      ·
        refine ⟨107478881035234127368987427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71652587356822751579324951 107478881035234127368987427)
        ·
          refine ⟨161218321552851191053481141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107478881035234127368987427 161218321552851191053481141)
          ·
            refine ⟨15114217645579799161263857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 161218321552851191053481141 15114217645579799161263857)
            ·
              refine ⟨11335663234184849370947893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15114217645579799161263857 11335663234184849370947893)
              ·
                refine ⟨1062718428204829628526365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11335663234184849370947893 1062718428204829628526365)
                ·
                  refine ⟨398519410576811110697387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1062718428204829628526365 398519410576811110697387)
                  ·
                    rfl

theorem cell21_1746256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 5, 3].length) (baseStart_1746256 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1746256 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1746256 prefixEnd_1746256 := by exact prefixLift 1746256
  have htrace : WordTrace (prefixWord ++ tailWord_1746256) baseStart_1746256 baseEnd_1746256 := by
    simpa [prefixWord, tailWord_1746256, baseEnd_1746256] using wordTrace_append hprefix tailTrace_1746256
  have hstable : (prefixWord ++ tailWord_1746256).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746256).length < 2 ^ (prefixWord ++ tailWord_1746256).sum := by decide
  have hdescent : baseEnd_1746256 < baseStart_1746256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746301 : List Nat := [1, 4, 1, 1, 2, 2, 5, 5]
def baseStart_1746301 : Nat := 118140960795 + 1746301 * 2 ^ 59
def prefixEnd_1746301 : Nat := 4983230072969 + 3 ^ 40 * 1746301 * 2
def baseEnd_1746301 : Nat := 132843226729967010815765

theorem tailTrace_1746301 : CollatzResearch.WordTrace tailWord_1746301 prefixEnd_1746301 132843226729967010815765 := by
  unfold tailWord_1746301
  simp only [CollatzResearch.WordTrace]
  refine ⟨63692830046457196311454757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42461886697638130874303171 63692830046457196311454757)
  ·
    refine ⟨11942405633710724308397767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63692830046457196311454757 11942405633710724308397767)
    ·
      refine ⟨17913608450566086462596651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11942405633710724308397767 17913608450566086462596651)
      ·
        refine ⟨26870412675849129693894977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17913608450566086462596651 26870412675849129693894977)
        ·
          refine ⟨20152809506886847270421233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26870412675849129693894977 20152809506886847270421233)
          ·
            refine ⟨15114607130165135452815925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20152809506886847270421233 15114607130165135452815925)
            ·
              refine ⟨1416994418452981448701493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15114607130165135452815925 1416994418452981448701493)
              ·
                refine ⟨132843226729967010815765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1416994418452981448701493 132843226729967010815765)
                ·
                  rfl

theorem cell21_1746301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 5].length) (baseStart_1746301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1746301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1746301 prefixEnd_1746301 := by exact prefixLift 1746301
  have htrace : WordTrace (prefixWord ++ tailWord_1746301) baseStart_1746301 baseEnd_1746301 := by
    simpa [prefixWord, tailWord_1746301, baseEnd_1746301] using wordTrace_append hprefix tailTrace_1746301
  have hstable : (prefixWord ++ tailWord_1746301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746301).length < 2 ^ (prefixWord ++ tailWord_1746301).sum := by decide
  have hdescent : baseEnd_1746301 < baseStart_1746301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746436 : List Nat := [2, 3, 2, 3, 11]
def baseStart_1746436 : Nat := 118140960795 + 1746436 * 2 ^ 59
def prefixEnd_1746436 : Nat := 4983230072969 + 3 ^ 40 * 1746436 * 2
def baseEnd_1746436 : Nat := 4920499864557664169099

theorem tailTrace_1746436 : CollatzResearch.WordTrace tailWord_1746436 prefixEnd_1746436 4920499864557664169099 := by
  unfold tailWord_1746436
  simp only [CollatzResearch.WordTrace]
  refine ⟨31848876950484057183809581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42465169267312076245079441 31848876950484057183809581)
  ·
    refine ⟨11943328856431521443928593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31848876950484057183809581 11943328856431521443928593)
    ·
      refine ⟨8957496642323641082946445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11943328856431521443928593 8957496642323641082946445)
      ·
        refine ⟨3359061240871365406104917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8957496642323641082946445 3359061240871365406104917)
        ·
          refine ⟨4920499864557664169099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3359061240871365406104917 4920499864557664169099)
          ·
            rfl

theorem cell21_1746436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 11].length) (baseStart_1746436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1746436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1746436 prefixEnd_1746436 := by exact prefixLift 1746436
  have htrace : WordTrace (prefixWord ++ tailWord_1746436) baseStart_1746436 baseEnd_1746436 := by
    simpa [prefixWord, tailWord_1746436, baseEnd_1746436] using wordTrace_append hprefix tailTrace_1746436
  have hstable : (prefixWord ++ tailWord_1746436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746436).length < 2 ^ (prefixWord ++ tailWord_1746436).sum := by decide
  have hdescent : baseEnd_1746436 < baseStart_1746436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746439 : List Nat := [1, 1, 4, 3, 2, 2, 2, 2, 4]
def baseStart_1746439 : Nat := 118140960795 + 1746439 * 2 ^ 59
def prefixEnd_1746439 : Nat := 4983230072969 + 3 ^ 40 * 1746439 * 2
def baseEnd_1746439 : Nat := 398561173670043459147013

theorem tailTrace_1746439 : CollatzResearch.WordTrace tailWord_1746439 prefixEnd_1746439 398561173670043459147013 := by
  unfold tailWord_1746439
  simp only [CollatzResearch.WordTrace]
  refine ⟨63697863319957245879978371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42465242213304830586652247 63697863319957245879978371)
  ·
    refine ⟨95546794979935868819967557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63697863319957245879978371 95546794979935868819967557)
    ·
      refine ⟨17915024058737975403743917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95546794979935868819967557 17915024058737975403743917)
      ·
        refine ⟨6718134022026740776403969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17915024058737975403743917 6718134022026740776403969)
        ·
          refine ⟨5038600516520055582302977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6718134022026740776403969 5038600516520055582302977)
          ·
            refine ⟨3778950387390041686727233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5038600516520055582302977 3778950387390041686727233)
            ·
              refine ⟨2834212790542531265045425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3778950387390041686727233 2834212790542531265045425)
              ·
                refine ⟨2125659592906898448784069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2834212790542531265045425 2125659592906898448784069)
                ·
                  refine ⟨398561173670043459147013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2125659592906898448784069 398561173670043459147013)
                  ·
                    rfl

theorem cell21_1746439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 2, 4].length) (baseStart_1746439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1746439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1746439 prefixEnd_1746439 := by exact prefixLift 1746439
  have htrace : WordTrace (prefixWord ++ tailWord_1746439) baseStart_1746439 baseEnd_1746439 := by
    simpa [prefixWord, tailWord_1746439, baseEnd_1746439] using wordTrace_append hprefix tailTrace_1746439
  have hstable : (prefixWord ++ tailWord_1746439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746439).length < 2 ^ (prefixWord ++ tailWord_1746439).sum := by decide
  have hdescent : baseEnd_1746439 < baseStart_1746439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746442 : List Nat := [3, 1, 2, 2, 2, 4, 2, 2, 3]
def baseStart_1746442 : Nat := 118140960795 + 1746442 * 2 ^ 59
def prefixEnd_1746442 : Nat := 4983230072969 + 3 ^ 40 * 1746442 * 2
def baseEnd_1746442 : Nat := 398561858310916120597007

theorem tailTrace_1746442 : CollatzResearch.WordTrace tailWord_1746442 prefixEnd_1746442 398561858310916120597007 := by
  unfold tailWord_1746442
  simp only [CollatzResearch.WordTrace]
  refine ⟨15924493184736594348084395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42465315159297584928225053 15924493184736594348084395)
  ·
    refine ⟨23886739777104891522126593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15924493184736594348084395 23886739777104891522126593)
    ·
      refine ⟨17915054832828668641594945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23886739777104891522126593 17915054832828668641594945)
      ·
        refine ⟨13436291124621501481196209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17915054832828668641594945 13436291124621501481196209)
        ·
          refine ⟨10077218343466126110897157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13436291124621501481196209 10077218343466126110897157)
          ·
            refine ⟨1889478439399898645793217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10077218343466126110897157 1889478439399898645793217)
            ·
              refine ⟨1417108829549923984344913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1889478439399898645793217 1417108829549923984344913)
              ·
                refine ⟨1062831622162442988258685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1417108829549923984344913 1062831622162442988258685)
                ·
                  refine ⟨398561858310916120597007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1062831622162442988258685 398561858310916120597007)
                  ·
                    rfl

theorem cell21_1746442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 2, 3].length) (baseStart_1746442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1746442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1746442 prefixEnd_1746442 := by exact prefixLift 1746442
  have htrace : WordTrace (prefixWord ++ tailWord_1746442) baseStart_1746442 baseEnd_1746442 := by
    simpa [prefixWord, tailWord_1746442, baseEnd_1746442] using wordTrace_append hprefix tailTrace_1746442
  have hstable : (prefixWord ++ tailWord_1746442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746442).length < 2 ^ (prefixWord ++ tailWord_1746442).sum := by decide
  have hdescent : baseEnd_1746442 < baseStart_1746442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746453 : List Nat := [1, 3, 2, 1, 3, 4, 1, 6]
def baseStart_1746453 : Nat := 118140960795 + 1746453 * 2 ^ 59
def prefixEnd_1746453 : Nat := 4983230072969 + 3 ^ 40 * 1746453 * 2
def baseEnd_1746453 : Nat := 132854789553594181971217

theorem tailTrace_1746453 : CollatzResearch.WordTrace tailWord_1746453 prefixEnd_1746453 132854789553594181971217 := by
  unfold tailWord_1746453
  simp only [CollatzResearch.WordTrace]
  refine ⟨63698373941906526270988013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42465582627937684180658675 63698373941906526270988013)
  ·
    refine ⟨23886890228214947351620505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63698373941906526270988013 23886890228214947351620505)
    ·
      refine ⟨17915167671161210513715379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23886890228214947351620505 17915167671161210513715379)
      ·
        refine ⟨26872751506741815770573069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17915167671161210513715379 26872751506741815770573069)
        ·
          refine ⟨10077281815028180913964901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26872751506741815770573069 10077281815028180913964901)
          ·
            refine ⟨1889490340317783921368419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10077281815028180913964901 1889490340317783921368419)
            ·
              refine ⟨2834235510476675882052629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1889490340317783921368419 2834235510476675882052629)
              ·
                refine ⟨132854789553594181971217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2834235510476675882052629 132854789553594181971217)
                ·
                  rfl

theorem cell21_1746453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 6].length) (baseStart_1746453 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1746453 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1746453 prefixEnd_1746453 := by exact prefixLift 1746453
  have htrace : WordTrace (prefixWord ++ tailWord_1746453) baseStart_1746453 baseEnd_1746453 := by
    simpa [prefixWord, tailWord_1746453, baseEnd_1746453] using wordTrace_append hprefix tailTrace_1746453
  have hstable : (prefixWord ++ tailWord_1746453).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746453).length < 2 ^ (prefixWord ++ tailWord_1746453).sum := by decide
  have hdescent : baseEnd_1746453 < baseStart_1746453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746481 : List Nat := [1, 2, 2, 3, 1, 1, 1, 4, 6]
def baseStart_1746481 : Nat := 118140960795 + 1746481 * 2 ^ 59
def prefixEnd_1746481 : Nat := 4983230072969 + 3 ^ 40 * 1746481 * 2
def baseEnd_1746481 : Nat := 398570758642260719446927

theorem tailTrace_1746481 : CollatzResearch.WordTrace tailWord_1746481 prefixEnd_1746481 398570758642260719446927 := by
  unfold tailWord_1746481
  simp only [CollatzResearch.WordTrace]
  refine ⟨63699395185805087053007297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42466263457203391368671531 63699395185805087053007297)
  ·
    refine ⟨47774546389353815289755473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63699395185805087053007297 47774546389353815289755473)
    ·
      refine ⟨35830909792015361467316605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47774546389353815289755473 35830909792015361467316605)
      ·
        refine ⟨13436591172005760550243727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35830909792015361467316605 13436591172005760550243727)
        ·
          refine ⟨20154886758008640825365591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13436591172005760550243727 20154886758008640825365591)
          ·
            refine ⟨30232330137012961238048387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20154886758008640825365591 30232330137012961238048387)
            ·
              refine ⟨45348495205519441857072581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30232330137012961238048387 45348495205519441857072581)
              ·
                refine ⟨8502842851034895348201109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45348495205519441857072581 8502842851034895348201109)
                ·
                  refine ⟨398570758642260719446927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8502842851034895348201109 398570758642260719446927)
                  ·
                    rfl

theorem cell21_1746481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 6].length) (baseStart_1746481 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1746481 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1746481 prefixEnd_1746481 := by exact prefixLift 1746481
  have htrace : WordTrace (prefixWord ++ tailWord_1746481) baseStart_1746481 baseEnd_1746481 := by
    simpa [prefixWord, tailWord_1746481, baseEnd_1746481] using wordTrace_append hprefix tailTrace_1746481
  have hstable : (prefixWord ++ tailWord_1746481).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746481).length < 2 ^ (prefixWord ++ tailWord_1746481).sum := by decide
  have hdescent : baseEnd_1746481 < baseStart_1746481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746636 : List Nat := [2, 2, 1, 5, 2, 1, 1, 2, 5]
def baseStart_1746636 : Nat := 118140960795 + 1746636 * 2 ^ 59
def prefixEnd_1746636 : Nat := 4983230072969 + 3 ^ 40 * 1746636 * 2
def baseEnd_1746636 : Nat := 398606131754014894363277

theorem tailTrace_1746636 : CollatzResearch.WordTrace tailWord_1746636 prefixEnd_1746636 398606131754014894363277 := by
  unfold tailWord_1746636
  simp only [CollatzResearch.WordTrace]
  refine ⟨31852524250121774262449881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42470032333495699016599841 31852524250121774262449881)
  ·
    refine ⟨23889393187591330696837411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31852524250121774262449881 23889393187591330696837411)
    ·
      refine ⟨35834089781386996045256117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23889393187591330696837411 35834089781386996045256117)
      ·
        refine ⟨3359445917005030879242761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35834089781386996045256117 3359445917005030879242761)
        ·
          refine ⟨2519584437753773159432071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3359445917005030879242761 2519584437753773159432071)
          ·
            refine ⟨3779376656630659739148107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2519584437753773159432071 3779376656630659739148107)
            ·
              refine ⟨5669064984945989608722161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3779376656630659739148107 5669064984945989608722161)
              ·
                refine ⟨4251798738709492206541621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5669064984945989608722161 4251798738709492206541621)
                ·
                  refine ⟨398606131754014894363277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4251798738709492206541621 398606131754014894363277)
                  ·
                    rfl

theorem cell21_1746636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 5].length) (baseStart_1746636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1746636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1746636 prefixEnd_1746636 := by exact prefixLift 1746636
  have htrace : WordTrace (prefixWord ++ tailWord_1746636) baseStart_1746636 baseEnd_1746636 := by
    simpa [prefixWord, tailWord_1746636, baseEnd_1746636] using wordTrace_append hprefix tailTrace_1746636
  have hstable : (prefixWord ++ tailWord_1746636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746636).length < 2 ^ (prefixWord ++ tailWord_1746636).sum := by decide
  have hdescent : baseEnd_1746636 < baseStart_1746636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746664 : List Nat := [2, 1, 4, 1, 3, 2, 8]
def baseStart_1746664 : Nat := 118140960795 + 1746664 * 2 ^ 59
def prefixEnd_1746664 : Nat := 4983230072969 + 3 ^ 40 * 1746664 * 2
def baseEnd_1746664 : Nat := 44290280192832563099617

theorem tailTrace_1746664 : CollatzResearch.WordTrace tailWord_1746664 prefixEnd_1746664 44290280192832563099617 := by
  unfold tailWord_1746664
  simp only [CollatzResearch.WordTrace]
  refine ⟨31853034872071054653459523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42470713162761406204612697 31853034872071054653459523)
  ·
    refine ⟨47779552308106581980189285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31853034872071054653459523 47779552308106581980189285)
    ·
      refine ⟨8958666057769984121285491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47779552308106581980189285 8958666057769984121285491)
      ·
        refine ⟨13437999086654976181928237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8958666057769984121285491 13437999086654976181928237)
        ·
          refine ⟨5039249657495616068223089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13437999086654976181928237 5039249657495616068223089)
          ·
            refine ⟨3779437243121712051167317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5039249657495616068223089 3779437243121712051167317)
            ·
              refine ⟨44290280192832563099617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3779437243121712051167317 44290280192832563099617)
              ·
                rfl

theorem cell21_1746664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 8].length) (baseStart_1746664 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1746664 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1746664 prefixEnd_1746664 := by exact prefixLift 1746664
  have htrace : WordTrace (prefixWord ++ tailWord_1746664) baseStart_1746664 baseEnd_1746664 := by
    simpa [prefixWord, tailWord_1746664, baseEnd_1746664] using wordTrace_append hprefix tailTrace_1746664
  have hstable : (prefixWord ++ tailWord_1746664).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746664).length < 2 ^ (prefixWord ++ tailWord_1746664).sum := by decide
  have hdescent : baseEnd_1746664 < baseStart_1746664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746709 : List Nat := [1, 3, 2, 1, 2, 3, 1, 2, 6]
def baseStart_1746709 : Nat := 118140960795 + 1746709 * 2 ^ 59
def prefixEnd_1746709 : Nat := 4983230072969 + 3 ^ 40 * 1746709 * 2
def baseEnd_1746709 : Nat := 398622791348582989646461

theorem tailTrace_1746709 : CollatzResearch.WordTrace tailWord_1746709 prefixEnd_1746709 398622791348582989646461 := by
  unfold tailWord_1746709
  simp only [CollatzResearch.WordTrace]
  refine ⟨63707711028979081992307181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42471807352652721328204787 63707711028979081992307181)
  ·
    refine ⟨23890391635867155747115193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63707711028979081992307181 23890391635867155747115193)
    ·
      refine ⟨17917793726900366810336395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23890391635867155747115193 17917793726900366810336395)
      ·
        refine ⟨26876690590350550215504593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17917793726900366810336395 26876690590350550215504593)
        ·
          refine ⟨20157517942762912661628445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26876690590350550215504593 20157517942762912661628445)
          ·
            refine ⟨7559069228536092248110667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20157517942762912661628445 7559069228536092248110667)
            ·
              refine ⟨11338603842804138372166001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7559069228536092248110667 11338603842804138372166001)
              ·
                refine ⟨8503952882103103779124501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11338603842804138372166001 8503952882103103779124501)
                ·
                  refine ⟨398622791348582989646461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8503952882103103779124501 398622791348582989646461)
                  ·
                    rfl

theorem cell21_1746709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 6].length) (baseStart_1746709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1746709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1746709 prefixEnd_1746709 := by exact prefixLift 1746709
  have htrace : WordTrace (prefixWord ++ tailWord_1746709) baseStart_1746709 baseEnd_1746709 := by
    simpa [prefixWord, tailWord_1746709, baseEnd_1746709] using wordTrace_append hprefix tailTrace_1746709
  have hstable : (prefixWord ++ tailWord_1746709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746709).length < 2 ^ (prefixWord ++ tailWord_1746709).sum := by decide
  have hdescent : baseEnd_1746709 < baseStart_1746709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746712 : List Nat := [2, 1, 2, 3, 1, 1, 5, 3, 3]
def baseStart_1746712 : Nat := 118140960795 + 1746712 * 2 ^ 59
def prefixEnd_1746712 : Nat := 4983230072969 + 3 ^ 40 * 1746712 * 2
def baseEnd_1746712 : Nat := 398623475989455651096455

theorem tailTrace_1746712 : CollatzResearch.WordTrace tailWord_1746712 prefixEnd_1746712 398623475989455651096455 := by
  unfold tailWord_1746712
  simp only [CollatzResearch.WordTrace]
  refine ⟨31853910223984106752333195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42471880298645475669777593 31853910223984106752333195)
  ·
    refine ⟨47780865335976160128499793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31853910223984106752333195 47780865335976160128499793)
    ·
      refine ⟨35835649001982120096374845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47780865335976160128499793 35835649001982120096374845)
      ·
        refine ⟨13438368375743295036140567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35835649001982120096374845 13438368375743295036140567)
        ·
          refine ⟨20157552563614942554210851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13438368375743295036140567 20157552563614942554210851)
          ·
            refine ⟨30236328845422413831316277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20157552563614942554210851 30236328845422413831316277)
            ·
              refine ⟨2834655829258351296685901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30236328845422413831316277 2834655829258351296685901)
              ·
                refine ⟨1062995935971881736257213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2834655829258351296685901 1062995935971881736257213)
                ·
                  refine ⟨398623475989455651096455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1062995935971881736257213 398623475989455651096455)
                  ·
                    rfl

theorem cell21_1746712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 3, 3].length) (baseStart_1746712 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1746712 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1746712 prefixEnd_1746712 := by exact prefixLift 1746712
  have htrace : WordTrace (prefixWord ++ tailWord_1746712) baseStart_1746712 baseEnd_1746712 := by
    simpa [prefixWord, tailWord_1746712, baseEnd_1746712] using wordTrace_append hprefix tailTrace_1746712
  have hstable : (prefixWord ++ tailWord_1746712).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746712).length < 2 ^ (prefixWord ++ tailWord_1746712).sum := by decide
  have hdescent : baseEnd_1746712 < baseStart_1746712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746723 : List Nat := [1, 1, 1, 4, 2, 1, 11]
def baseStart_1746723 : Nat := 118140960795 + 1746723 * 2 ^ 59
def prefixEnd_1746723 : Nat := 4983230072969 + 3 ^ 40 * 1746723 * 2
def baseEnd_1746723 : Nat := 44291776259924675157011

theorem tailTrace_1746723 : CollatzResearch.WordTrace tailWord_1746723 prefixEnd_1746723 44291776259924675157011 := by
  unfold tailWord_1746723
  simp only [CollatzResearch.WordTrace]
  refine ⟨63708221650928362383316823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42472147767285574922211215 63708221650928362383316823)
  ·
    refine ⟨95562332476392543574975235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63708221650928362383316823 95562332476392543574975235)
    ·
      refine ⟨143343498714588815362462853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95562332476392543574975235 143343498714588815362462853)
      ·
        refine ⟨26876906008985402880461785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143343498714588815362462853 26876906008985402880461785)
        ·
          refine ⟨20157679506739052160346339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26876906008985402880461785 20157679506739052160346339)
          ·
            refine ⟨30236519260108578240519509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20157679506739052160346339 30236519260108578240519509)
            ·
              refine ⟨44291776259924675157011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 30236519260108578240519509 44291776259924675157011)
              ·
                rfl

theorem cell21_1746723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 11].length) (baseStart_1746723 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1746723 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1746723 prefixEnd_1746723 := by exact prefixLift 1746723
  have htrace : WordTrace (prefixWord ++ tailWord_1746723) baseStart_1746723 baseEnd_1746723 := by
    simpa [prefixWord, tailWord_1746723, baseEnd_1746723] using wordTrace_append hprefix tailTrace_1746723
  have hstable : (prefixWord ++ tailWord_1746723).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746723).length < 2 ^ (prefixWord ++ tailWord_1746723).sum := by decide
  have hdescent : baseEnd_1746723 < baseStart_1746723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746816 : List Nat := [2, 1, 1, 2, 1, 2, 7, 5]
def baseStart_1746816 : Nat := 118140960795 + 1746816 * 2 ^ 59
def prefixEnd_1746816 : Nat := 4983230072969 + 3 ^ 40 * 1746816 * 2
def baseEnd_1746816 : Nat := 132882403402124860454303

theorem tailTrace_1746816 : CollatzResearch.WordTrace tailWord_1746816 prefixEnd_1746816 132882403402124860454303 := by
  unfold tailWord_1746816
  simp only [CollatzResearch.WordTrace]
  refine ⟨31855806819795719633226151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42474409093060959510968201 31855806819795719633226151)
  ·
    refine ⟨47783710229693579449839227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31855806819795719633226151 47783710229693579449839227)
    ·
      refine ⟨71675565344540369174758841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47783710229693579449839227 71675565344540369174758841)
      ·
        refine ⟨53756674008405276881069131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71675565344540369174758841 53756674008405276881069131)
        ·
          refine ⟨80635011012607915321603697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53756674008405276881069131 80635011012607915321603697)
          ·
            refine ⟨60476258259455936491202773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80635011012607915321603697 60476258259455936491202773)
            ·
              refine ⟨1417412302955998511512565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 60476258259455936491202773 1417412302955998511512565)
              ·
                refine ⟨132882403402124860454303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1417412302955998511512565 132882403402124860454303)
                ·
                  rfl

theorem cell21_1746816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 5].length) (baseStart_1746816 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1746816 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1746816 prefixEnd_1746816 := by exact prefixLift 1746816
  have htrace : WordTrace (prefixWord ++ tailWord_1746816) baseStart_1746816 baseEnd_1746816 := by
    simpa [prefixWord, tailWord_1746816, baseEnd_1746816] using wordTrace_append hprefix tailTrace_1746816
  have hstable : (prefixWord ++ tailWord_1746816).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746816).length < 2 ^ (prefixWord ++ tailWord_1746816).sum := by decide
  have hdescent : baseEnd_1746816 < baseStart_1746816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746892 : List Nat := [2, 2, 1, 4, 1, 4, 7]
def baseStart_1746892 : Nat := 118140960795 + 1746892 * 2 ^ 59
def prefixEnd_1746892 : Nat := 4983230072969 + 3 ^ 40 * 1746892 * 2
def baseEnd_1746892 : Nat := 44296061604646148677343

theorem tailTrace_1746892 : CollatzResearch.WordTrace tailWord_1746892 prefixEnd_1746892 44296061604646148677343 := by
  unfold tailWord_1746892
  simp only [CollatzResearch.WordTrace]
  refine ⟨31857192793658052123109465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42476257058210736164145953 31857192793658052123109465)
  ·
    refine ⟨23892894595243539092332099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31857192793658052123109465 23892894595243539092332099)
    ·
      refine ⟨35839341892865308638498149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23892894595243539092332099 35839341892865308638498149)
      ·
        refine ⟨6719876604912245369718403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35839341892865308638498149 6719876604912245369718403)
        ·
          refine ⟨10079814907368368054577605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6719876604912245369718403 10079814907368368054577605)
          ·
            refine ⟨1889965295131569010233301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10079814907368368054577605 1889965295131569010233301)
            ·
              refine ⟨44296061604646148677343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1889965295131569010233301 44296061604646148677343)
              ·
                rfl

theorem cell21_1746892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 7].length) (baseStart_1746892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1746892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1746892 prefixEnd_1746892 := by exact prefixLift 1746892
  have htrace : WordTrace (prefixWord ++ tailWord_1746892) baseStart_1746892 baseEnd_1746892 := by
    simpa [prefixWord, tailWord_1746892, baseEnd_1746892] using wordTrace_append hprefix tailTrace_1746892
  have hstable : (prefixWord ++ tailWord_1746892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746892).length < 2 ^ (prefixWord ++ tailWord_1746892).sum := by decide
  have hdescent : baseEnd_1746892 < baseStart_1746892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746898 : List Nat := [3, 2, 2, 3, 2, 1, 3, 2, 3]
def baseStart_1746898 : Nat := 118140960795 + 1746898 * 2 ^ 59
def prefixEnd_1746898 : Nat := 4983230072969 + 3 ^ 40 * 1746898 * 2
def baseEnd_1746898 : Nat := 398665923723560660996075

theorem tailTrace_1746898 : CollatzResearch.WordTrace tailWord_1746898 prefixEnd_1746898 398665923723560660996075 := by
  unfold tailWord_1746898
  simp only [CollatzResearch.WordTrace]
  refine ⟨15928651106323591817734337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42476402950196244847291565 15928651106323591817734337)
  ·
    refine ⟨11946488329742693863300753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15928651106323591817734337 11946488329742693863300753)
    ·
      refine ⟨8959866247307020397475565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11946488329742693863300753 8959866247307020397475565)
      ·
        refine ⟨3359949842740132649053337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8959866247307020397475565 3359949842740132649053337)
        ·
          refine ⟨2519962382055099486790003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3359949842740132649053337 2519962382055099486790003)
          ·
            refine ⟨3779943573082649230185005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2519962382055099486790003 3779943573082649230185005)
            ·
              refine ⟨1417478839905993461319377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3779943573082649230185005 1417478839905993461319377)
              ·
                refine ⟨1063109129929495095989533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1417478839905993461319377 1063109129929495095989533)
                ·
                  refine ⟨398665923723560660996075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1063109129929495095989533 398665923723560660996075)
                  ·
                    rfl

theorem cell21_1746898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 2, 3].length) (baseStart_1746898 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1746898 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1746898 prefixEnd_1746898 := by exact prefixLift 1746898
  have htrace : WordTrace (prefixWord ++ tailWord_1746898) baseStart_1746898 baseEnd_1746898 := by
    simpa [prefixWord, tailWord_1746898, baseEnd_1746898] using wordTrace_append hprefix tailTrace_1746898
  have hstable : (prefixWord ++ tailWord_1746898).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746898).length < 2 ^ (prefixWord ++ tailWord_1746898).sum := by decide
  have hdescent : baseEnd_1746898 < baseStart_1746898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746909 : List Nat := [1, 4, 3, 1, 3, 1, 2, 6]
def baseStart_1746909 : Nat := 118140960795 + 1746909 * 2 ^ 59
def prefixEnd_1746909 : Nat := 4983230072969 + 3 ^ 40 * 1746909 * 2
def baseEnd_1746909 : Nat := 132889478024475695437573

theorem tailTrace_1746909 : CollatzResearch.WordTrace tailWord_1746909 prefixEnd_1746909 132889478024475695437573 := by
  unfold tailWord_1746909
  simp only [CollatzResearch.WordTrace]
  refine ⟨63715005628254516149587781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42476670418836344099725187 63715005628254516149587781)
  ·
    refine ⟨11946563555297721778047709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63715005628254516149587781 11946563555297721778047709)
    ·
      refine ⟨4479961333236645666767891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11946563555297721778047709 4479961333236645666767891)
      ·
        refine ⟨6719941999854968500151837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4479961333236645666767891 6719941999854968500151837)
        ·
          refine ⟨2519978249945613187556939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6719941999854968500151837 2519978249945613187556939)
          ·
            refine ⟨3779967374918419781335409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2519978249945613187556939 3779967374918419781335409)
            ·
              refine ⟨2834975531188814836001557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3779967374918419781335409 2834975531188814836001557)
              ·
                refine ⟨132889478024475695437573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2834975531188814836001557 132889478024475695437573)
                ·
                  rfl

theorem cell21_1746909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 6].length) (baseStart_1746909 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1746909 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1746909 prefixEnd_1746909 := by exact prefixLift 1746909
  have htrace : WordTrace (prefixWord ++ tailWord_1746909) baseStart_1746909 baseEnd_1746909 := by
    simpa [prefixWord, tailWord_1746909, baseEnd_1746909] using wordTrace_append hprefix tailTrace_1746909
  have hstable : (prefixWord ++ tailWord_1746909).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746909).length < 2 ^ (prefixWord ++ tailWord_1746909).sum := by decide
  have hdescent : baseEnd_1746909 < baseStart_1746909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746951 : List Nat := [1, 1, 4, 3, 1, 11]
def baseStart_1746951 : Nat := 118140960795 + 1746951 * 2 ^ 59
def prefixEnd_1746951 : Nat := 4983230072969 + 3 ^ 40 * 1746951 * 2
def baseEnd_1746951 : Nat := 14765852557246086911579

theorem tailTrace_1746951 : CollatzResearch.WordTrace tailWord_1746951 prefixEnd_1746951 14765852557246086911579 := by
  unfold tailWord_1746951
  simp only [CollatzResearch.WordTrace]
  refine ⟨63716537494102357322616707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42477691662734904881744471 63716537494102357322616707)
  ·
    refine ⟨95574806241153535983925061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63716537494102357322616707 95574806241153535983925061)
    ·
      refine ⟨17920276170216287996985949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95574806241153535983925061 17920276170216287996985949)
      ·
        refine ⟨6720103563831107998869731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17920276170216287996985949 6720103563831107998869731)
        ·
          refine ⟨10080155345746661998304597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6720103563831107998869731 10080155345746661998304597)
          ·
            refine ⟨14765852557246086911579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10080155345746661998304597 14765852557246086911579)
            ·
              rfl

theorem cell21_1746951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 11].length) (baseStart_1746951 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1746951 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1746951 prefixEnd_1746951 := by exact prefixLift 1746951
  have htrace : WordTrace (prefixWord ++ tailWord_1746951) baseStart_1746951 baseEnd_1746951 := by
    simpa [prefixWord, tailWord_1746951, baseEnd_1746951] using wordTrace_append hprefix tailTrace_1746951
  have hstable : (prefixWord ++ tailWord_1746951).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746951).length < 2 ^ (prefixWord ++ tailWord_1746951).sum := by decide
  have hdescent : baseEnd_1746951 < baseStart_1746951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1746999 : List Nat := [1, 1, 3, 1, 2, 2, 3, 5, 3]
def baseStart_1746999 : Nat := 118140960795 + 1746999 * 2 ^ 59
def prefixEnd_1746999 : Nat := 4983230072969 + 3 ^ 40 * 1746999 * 2
def baseEnd_1746999 : Nat := 398688973299606929812535

theorem tailTrace_1746999 : CollatzResearch.WordTrace tailWord_1746999 prefixEnd_1746999 398688973299606929812535 := by
  unfold tailWord_1746999
  simp only [CollatzResearch.WordTrace]
  refine ⟨63718288197928461520364051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42478858798618974346909367 63718288197928461520364051)
  ·
    refine ⟨95577432296892692280546077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63718288197928461520364051 95577432296892692280546077)
    ·
      refine ⟨35841537111334759605204779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95577432296892692280546077 35841537111334759605204779)
      ·
        refine ⟨53762305667002139407807169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35841537111334759605204779 53762305667002139407807169)
        ·
          refine ⟨40321729250251604555855377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53762305667002139407807169 40321729250251604555855377)
          ·
            refine ⟨30241296937688703416891533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40321729250251604555855377 30241296937688703416891533)
            ·
              refine ⟨11340486351633263781334325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30241296937688703416891533 11340486351633263781334325)
              ·
                refine ⟨1063170595465618479500093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11340486351633263781334325 1063170595465618479500093)
                ·
                  refine ⟨398688973299606929812535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1063170595465618479500093 398688973299606929812535)
                  ·
                    rfl

theorem cell21_1746999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 5, 3].length) (baseStart_1746999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1746999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1746999 prefixEnd_1746999 := by exact prefixLift 1746999
  have htrace : WordTrace (prefixWord ++ tailWord_1746999) baseStart_1746999 baseEnd_1746999 := by
    simpa [prefixWord, tailWord_1746999, baseEnd_1746999] using wordTrace_append hprefix tailTrace_1746999
  have hstable : (prefixWord ++ tailWord_1746999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1746999).length < 2 ^ (prefixWord ++ tailWord_1746999).sum := by decide
  have hdescent : baseEnd_1746999 < baseStart_1746999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1746999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747044 : List Nat := [2, 3, 1, 1, 2, 1, 6, 5]
def baseStart_1747044 : Nat := 118140960795 + 1747044 * 2 ^ 59
def prefixEnd_1747044 : Nat := 4983230072969 + 3 ^ 40 * 1747044 * 2
def baseEnd_1747044 : Nat := 132899747637565617187481

theorem tailTrace_1747044 : CollatzResearch.WordTrace tailWord_1747044 prefixEnd_1747044 132899747637565617187481 := by
  unfold tailWord_1747044
  simp only [CollatzResearch.WordTrace]
  refine ⟨31859964741382717102876093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42479952988510289470501457 31859964741382717102876093)
  ·
    refine ⟨11947486778018518913578535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31859964741382717102876093 11947486778018518913578535)
    ·
      refine ⟨17921230167027778370367803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11947486778018518913578535 17921230167027778370367803)
      ·
        refine ⟨26881845250541667555551705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17921230167027778370367803 26881845250541667555551705)
        ·
          refine ⟨20161383937906250666663779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26881845250541667555551705 20161383937906250666663779)
          ·
            refine ⟨30242075906859375999995669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20161383937906250666663779 30242075906859375999995669)
            ·
              refine ⟨1417597308134033249999797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30242075906859375999995669 1417597308134033249999797)
              ·
                refine ⟨132899747637565617187481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1417597308134033249999797 132899747637565617187481)
                ·
                  rfl

theorem cell21_1747044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 5].length) (baseStart_1747044 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1747044 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1747044 prefixEnd_1747044 := by exact prefixLift 1747044
  have htrace : WordTrace (prefixWord ++ tailWord_1747044) baseStart_1747044 baseEnd_1747044 := by
    simpa [prefixWord, tailWord_1747044, baseEnd_1747044] using wordTrace_append hprefix tailTrace_1747044
  have hstable : (prefixWord ++ tailWord_1747044).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747044).length < 2 ^ (prefixWord ++ tailWord_1747044).sum := by decide
  have hdescent : baseEnd_1747044 < baseStart_1747044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747050 : List Nat := [3, 1, 3, 2, 4, 1, 1, 3, 3]
def baseStart_1747050 : Nat := 118140960795 + 1747050 * 2 ^ 59
def prefixEnd_1747050 : Nat := 4983230072969 + 3 ^ 40 * 1747050 * 2
def baseEnd_1747050 : Nat := 398700612194442174462431

theorem tailTrace_1747050 : CollatzResearch.WordTrace tailWord_1747050 prefixEnd_1747050 398700612194442174462431 := by
  unfold tailWord_1747050
  simp only [CollatzResearch.WordTrace]
  refine ⟨15930037080185924307617651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42480098880495798153647069 15930037080185924307617651)
  ·
    refine ⟨23895055620278886461426477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15930037080185924307617651 23895055620278886461426477)
    ·
      refine ⟨8960645857604582423034929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23895055620278886461426477 8960645857604582423034929)
      ·
        refine ⟨6720484393203436817276197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8960645857604582423034929 6720484393203436817276197)
        ·
          refine ⟨1260090823725644403239287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6720484393203436817276197 1260090823725644403239287)
          ·
            refine ⟨1890136235588466604858931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1260090823725644403239287 1890136235588466604858931)
            ·
              refine ⟨2835204353382699907288397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1890136235588466604858931 2835204353382699907288397)
              ·
                refine ⟨1063201632518512465233149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2835204353382699907288397 1063201632518512465233149)
                ·
                  refine ⟨398700612194442174462431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1063201632518512465233149 398700612194442174462431)
                  ·
                    rfl

theorem cell21_1747050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 3, 3].length) (baseStart_1747050 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1747050 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1747050 prefixEnd_1747050 := by exact prefixLift 1747050
  have htrace : WordTrace (prefixWord ++ tailWord_1747050) baseStart_1747050 baseEnd_1747050 := by
    simpa [prefixWord, tailWord_1747050, baseEnd_1747050] using wordTrace_append hprefix tailTrace_1747050
  have hstable : (prefixWord ++ tailWord_1747050).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747050).length < 2 ^ (prefixWord ++ tailWord_1747050).sum := by decide
  have hdescent : baseEnd_1747050 < baseStart_1747050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747075 : List Nat := [1, 1, 1, 3, 3, 5, 1, 1, 5]
def baseStart_1747075 : Nat := 118140960795 + 1747075 * 2 ^ 59
def prefixEnd_1747075 : Nat := 4983230072969 + 3 ^ 40 * 1747075 * 2
def baseEnd_1747075 : Nat := 398706317535047686545713

theorem tailTrace_1747075 : CollatzResearch.WordTrace tailWord_1747075 prefixEnd_1747075 398706317535047686545713 := by
  unfold tailWord_1747075
  simp only [CollatzResearch.WordTrace]
  refine ⟨63721060145653126500130679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42480706763768751000087119 63721060145653126500130679)
  ·
    refine ⟨95581590218479689750196019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63721060145653126500130679 95581590218479689750196019)
    ·
      refine ⟨143372385327719534625294029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95581590218479689750196019 143372385327719534625294029)
      ·
        refine ⟨53764644497894825484485261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143372385327719534625294029 53764644497894825484485261)
        ·
          refine ⟨20161741686710559556681973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53764644497894825484485261 20161741686710559556681973)
          ·
            refine ⟨1890163283129114958438935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20161741686710559556681973 1890163283129114958438935)
            ·
              refine ⟨2835244924693672437658403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1890163283129114958438935 2835244924693672437658403)
              ·
                refine ⟨4252867387040508656487605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2835244924693672437658403 4252867387040508656487605)
                ·
                  refine ⟨398706317535047686545713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4252867387040508656487605 398706317535047686545713)
                  ·
                    rfl

theorem cell21_1747075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 5].length) (baseStart_1747075 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1747075 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1747075 prefixEnd_1747075 := by exact prefixLift 1747075
  have htrace : WordTrace (prefixWord ++ tailWord_1747075) baseStart_1747075 baseEnd_1747075 := by
    simpa [prefixWord, tailWord_1747075, baseEnd_1747075] using wordTrace_append hprefix tailTrace_1747075
  have hstable : (prefixWord ++ tailWord_1747075).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747075).length < 2 ^ (prefixWord ++ tailWord_1747075).sum := by decide
  have hdescent : baseEnd_1747075 < baseStart_1747075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747210 : List Nat := [3, 1, 2, 2, 1, 1, 4, 2, 5]
def baseStart_1747210 : Nat := 118140960795 + 1747210 * 2 ^ 59
def prefixEnd_1747210 : Nat := 4983230072969 + 3 ^ 40 * 1747210 * 2
def baseEnd_1747210 : Nat := 398737126374317451795437

theorem tailTrace_1747210 : CollatzResearch.WordTrace tailWord_1747210 prefixEnd_1747210 398737126374317451795437 := by
  unfold tailWord_1747210
  simp only [CollatzResearch.WordTrace]
  refine ⟨15931496000041011139073771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42483989333442696370863389 15931496000041011139073771)
  ·
    refine ⟨23897244000061516708610657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15931496000041011139073771 23897244000061516708610657)
    ·
      refine ⟨17922933000046137531457993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23897244000061516708610657 17922933000046137531457993)
      ·
        refine ⟨13442199750034603148593495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17922933000046137531457993 13442199750034603148593495)
        ·
          refine ⟨20163299625051904722890243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13442199750034603148593495 20163299625051904722890243)
          ·
            refine ⟨30244949437577857084335365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20163299625051904722890243 30244949437577857084335365)
            ·
              refine ⟨5670928019545848203312881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30244949437577857084335365 5670928019545848203312881)
              ·
                refine ⟨4253196014659386152484661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5670928019545848203312881 4253196014659386152484661)
                ·
                  refine ⟨398737126374317451795437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4253196014659386152484661 398737126374317451795437)
                  ·
                    rfl

theorem cell21_1747210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 5].length) (baseStart_1747210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1747210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1747210 prefixEnd_1747210 := by exact prefixLift 1747210
  have htrace : WordTrace (prefixWord ++ tailWord_1747210) baseStart_1747210 baseEnd_1747210 := by
    simpa [prefixWord, tailWord_1747210, baseEnd_1747210] using wordTrace_append hprefix tailTrace_1747210
  have hstable : (prefixWord ++ tailWord_1747210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747210).length < 2 ^ (prefixWord ++ tailWord_1747210).sum := by decide
  have hdescent : baseEnd_1747210 < baseStart_1747210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747224 : List Nat := [2, 1, 2, 3, 1, 2, 1, 1, 8]
def baseStart_1747224 : Nat := 118140960795 + 1747224 * 2 ^ 59
def prefixEnd_1747224 : Nat := 4983230072969 + 3 ^ 40 * 1747224 * 2
def baseEnd_1747224 : Nat := 398740321365056538562075

theorem tailTrace_1747224 : CollatzResearch.WordTrace tailWord_1747224 prefixEnd_1747224 398740321365056538562075 := by
  unfold tailWord_1747224
  simp only [CollatzResearch.WordTrace]
  refine ⟨31863247311056662473652363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42484329748075549964869817 31863247311056662473652363)
  ·
    refine ⟨47794870966584993710478545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31863247311056662473652363 47794870966584993710478545)
    ·
      refine ⟨35846153224938745282858909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47794870966584993710478545 35846153224938745282858909)
      ·
        refine ⟨13442307459352029481072091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35846153224938745282858909 13442307459352029481072091)
        ·
          refine ⟨20163461189028044221608137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13442307459352029481072091 20163461189028044221608137)
          ·
            refine ⟨15122595891771033166206103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20163461189028044221608137 15122595891771033166206103)
            ·
              refine ⟨22683893837656549749309155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15122595891771033166206103 22683893837656549749309155)
              ·
                refine ⟨34025840756484824623963733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22683893837656549749309155 34025840756484824623963733)
                ·
                  refine ⟨398740321365056538562075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34025840756484824623963733 398740321365056538562075)
                  ·
                    rfl

theorem cell21_1747224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 8].length) (baseStart_1747224 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1747224 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1747224 prefixEnd_1747224 := by exact prefixLift 1747224
  have htrace : WordTrace (prefixWord ++ tailWord_1747224) baseStart_1747224 baseEnd_1747224 := by
    simpa [prefixWord, tailWord_1747224, baseEnd_1747224] using wordTrace_append hprefix tailTrace_1747224
  have hstable : (prefixWord ++ tailWord_1747224).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747224).length < 2 ^ (prefixWord ++ tailWord_1747224).sum := by decide
  have hdescent : baseEnd_1747224 < baseStart_1747224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747227 : List Nat := [1, 1, 1, 1, 1, 1, 9, 3, 3]
def baseStart_1747227 : Nat := 118140960795 + 1747227 * 2 ^ 59
def prefixEnd_1747227 : Nat := 4983230072969 + 3 ^ 40 * 1747227 * 2
def baseEnd_1747227 : Nat := 398741006005929200012069

theorem tailTrace_1747227 : CollatzResearch.WordTrace tailWord_1747227 prefixEnd_1747227 398741006005929200012069 := by
  unfold tailWord_1747227
  simp only [CollatzResearch.WordTrace]
  refine ⟨63726604041102456459663935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42484402694068304306442623 63726604041102456459663935)
  ·
    refine ⟨95589906061653684689495903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63726604041102456459663935 95589906061653684689495903)
    ·
      refine ⟨143384859092480527034243855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95589906061653684689495903 143384859092480527034243855)
      ·
        refine ⟨215077288638720790551365783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143384859092480527034243855 215077288638720790551365783)
        ·
          refine ⟨322615932958081185827048675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215077288638720790551365783 322615932958081185827048675)
          ·
            refine ⟨483923899437121778740573013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322615932958081185827048675 483923899437121778740573013)
            ·
              refine ⟨2835491598264385422308045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 483923899437121778740573013 2835491598264385422308045)
              ·
                refine ⟨1063309349349144533365517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2835491598264385422308045 1063309349349144533365517)
                ·
                  refine ⟨398741006005929200012069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1063309349349144533365517 398741006005929200012069)
                  ·
                    rfl

theorem cell21_1747227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 3, 3].length) (baseStart_1747227 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1747227 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1747227 prefixEnd_1747227 := by exact prefixLift 1747227
  have htrace : WordTrace (prefixWord ++ tailWord_1747227) baseStart_1747227 baseEnd_1747227 := by
    simpa [prefixWord, tailWord_1747227, baseEnd_1747227] using wordTrace_append hprefix tailTrace_1747227
  have hstable : (prefixWord ++ tailWord_1747227).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747227).length < 2 ^ (prefixWord ++ tailWord_1747227).sum := by decide
  have hdescent : baseEnd_1747227 < baseStart_1747227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747258 : List Nat := [3, 1, 1, 1, 4, 2, 4, 1, 4]
def baseStart_1747258 : Nat := 118140960795 + 1747258 * 2 ^ 59
def prefixEnd_1747258 : Nat := 4983230072969 + 3 ^ 40 * 1747258 * 2
def baseEnd_1747258 : Nat := 398748080628280034995339

theorem tailTrace_1747258 : CollatzResearch.WordTrace tailWord_1747258 prefixEnd_1747258 398748080628280034995339 := by
  unfold tailWord_1747258
  simp only [CollatzResearch.WordTrace]
  refine ⟨15931933675997537188510607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42485156469326765836028285 15931933675997537188510607)
  ·
    refine ⟨23897900513996305782765911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15931933675997537188510607 23897900513996305782765911)
    ·
      refine ⟨35846850770994458674148867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23897900513996305782765911 35846850770994458674148867)
      ·
        refine ⟨53770276156491688011223301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35846850770994458674148867 53770276156491688011223301)
        ·
          refine ⟨10081926779342191502104369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53770276156491688011223301 10081926779342191502104369)
          ·
            refine ⟨7561445084506643626578277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10081926779342191502104369 7561445084506643626578277)
            ·
              refine ⟨1417770953344995679983427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7561445084506643626578277 1417770953344995679983427)
              ·
                refine ⟨2126656430017493519975141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1417770953344995679983427 2126656430017493519975141)
                ·
                  refine ⟨398748080628280034995339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2126656430017493519975141 398748080628280034995339)
                  ·
                    rfl

theorem cell21_1747258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 1, 4].length) (baseStart_1747258 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1747258 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1747258 prefixEnd_1747258 := by exact prefixLift 1747258
  have htrace : WordTrace (prefixWord ++ tailWord_1747258) baseStart_1747258 baseEnd_1747258 := by
    simpa [prefixWord, tailWord_1747258, baseEnd_1747258] using wordTrace_append hprefix tailTrace_1747258
  have hstable : (prefixWord ++ tailWord_1747258).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747258).length < 2 ^ (prefixWord ++ tailWord_1747258).sum := by decide
  have hdescent : baseEnd_1747258 < baseStart_1747258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747348 : List Nat := [2, 4, 2, 1, 3, 1, 8]
def baseStart_1747348 : Nat := 118140960795 + 1747348 * 2 ^ 59
def prefixEnd_1747348 : Nat := 4983230072969 + 3 ^ 40 * 1747348 * 2
def baseEnd_1747348 : Nat := 44307624428273319832795

theorem tailTrace_1747348 : CollatzResearch.WordTrace tailWord_1747348 prefixEnd_1747348 44307624428273319832795 := by
  unfold tailWord_1747348
  simp only [CollatzResearch.WordTrace]
  refine ⟨31865508636832047062409349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42487344849109396083212465 31865508636832047062409349)
  ·
    refine ⟨5974782869406008824201753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31865508636832047062409349 5974782869406008824201753)
    ·
      refine ⟨4481087152054506618151315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5974782869406008824201753 4481087152054506618151315)
      ·
        refine ⟨6721630728081759927226973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4481087152054506618151315 6721630728081759927226973)
        ·
          refine ⟨2520611523030659972710115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6721630728081759927226973 2520611523030659972710115)
          ·
            refine ⟨3780917284545989959065173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2520611523030659972710115 3780917284545989959065173)
            ·
              refine ⟨44307624428273319832795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3780917284545989959065173 44307624428273319832795)
              ·
                rfl

theorem cell21_1747348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 8].length) (baseStart_1747348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1747348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1747348 prefixEnd_1747348 := by exact prefixLift 1747348
  have htrace : WordTrace (prefixWord ++ tailWord_1747348) baseStart_1747348 baseEnd_1747348 := by
    simpa [prefixWord, tailWord_1747348, baseEnd_1747348] using wordTrace_append hprefix tailTrace_1747348
  have hstable : (prefixWord ++ tailWord_1747348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747348).length < 2 ^ (prefixWord ++ tailWord_1747348).sum := by decide
  have hdescent : baseEnd_1747348 < baseStart_1747348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747427 : List Nat := [1, 1, 1, 6, 3, 2, 2, 1, 4]
def baseStart_1747427 : Nat := 118140960795 + 1747427 * 2 ^ 59
def prefixEnd_1747427 : Nat := 4983230072969 + 3 ^ 40 * 1747427 * 2
def baseEnd_1747427 : Nat := 398786648730773296678327

theorem tailTrace_1747427 : CollatzResearch.WordTrace tailWord_1747427 prefixEnd_1747427 398786648730773296678327 := by
  unfold tailWord_1747427
  simp only [CollatzResearch.WordTrace]
  refine ⟨63733898640377890616944535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42489265760251927077963023 63733898640377890616944535)
  ·
    refine ⟨95600847960566835925416803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63733898640377890616944535 95600847960566835925416803)
    ·
      refine ⟨143401271940850253888125205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95600847960566835925416803 143401271940850253888125205)
      ·
        refine ⟨6721934622227355651005869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 143401271940850253888125205 6721934622227355651005869)
        ·
          refine ⟨2520725483335258369127201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6721934622227355651005869 2520725483335258369127201)
          ·
            refine ⟨1890544112501443776845401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2520725483335258369127201 1890544112501443776845401)
            ·
              refine ⟨1417908084376082832634051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1890544112501443776845401 1417908084376082832634051)
              ·
                refine ⟨2126862126564124248951077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1417908084376082832634051 2126862126564124248951077)
                ·
                  refine ⟨398786648730773296678327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2126862126564124248951077 398786648730773296678327)
                  ·
                    rfl

theorem cell21_1747427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 1, 4].length) (baseStart_1747427 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1747427 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1747427 prefixEnd_1747427 := by exact prefixLift 1747427
  have htrace : WordTrace (prefixWord ++ tailWord_1747427) baseStart_1747427 baseEnd_1747427 := by
    simpa [prefixWord, tailWord_1747427, baseEnd_1747427] using wordTrace_append hprefix tailTrace_1747427
  have hstable : (prefixWord ++ tailWord_1747427).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747427).length < 2 ^ (prefixWord ++ tailWord_1747427).sum := by decide
  have hdescent : baseEnd_1747427 < baseStart_1747427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747652 : List Nat := [2, 3, 3, 1, 1, 4, 1, 6]
def baseStart_1747652 : Nat := 118140960795 + 1747652 * 2 ^ 59
def prefixEnd_1747652 : Nat := 4983230072969 + 3 ^ 40 * 1747652 * 2
def baseEnd_1747652 : Nat := 132945998932074301809289

theorem tailTrace_1747652 : CollatzResearch.WordTrace tailWord_1747652 prefixEnd_1747652 132945998932074301809289 := by
  unfold tailWord_1747652
  simp only [CollatzResearch.WordTrace]
  refine ⟨31871052532281377021942605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42494736709708502695923473 31871052532281377021942605)
  ·
    refine ⟨11951644699605516383228477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31871052532281377021942605 11951644699605516383228477)
    ·
      refine ⟨4481866762352068643710679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11951644699605516383228477 4481866762352068643710679)
      ·
        refine ⟨6722800143528102965566019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4481866762352068643710679 6722800143528102965566019)
        ·
          refine ⟨10084200215292154448349029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6722800143528102965566019 10084200215292154448349029)
          ·
            refine ⟨1890787540367278959065443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10084200215292154448349029 1890787540367278959065443)
            ·
              refine ⟨2836181310550918438598165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1890787540367278959065443 2836181310550918438598165)
              ·
                refine ⟨132945998932074301809289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2836181310550918438598165 132945998932074301809289)
                ·
                  rfl

theorem cell21_1747652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 6].length) (baseStart_1747652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1747652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1747652 prefixEnd_1747652 := by exact prefixLift 1747652
  have htrace : WordTrace (prefixWord ++ tailWord_1747652) baseStart_1747652 baseEnd_1747652 := by
    simpa [prefixWord, tailWord_1747652, baseEnd_1747652] using wordTrace_append hprefix tailTrace_1747652
  have hstable : (prefixWord ++ tailWord_1747652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747652).length < 2 ^ (prefixWord ++ tailWord_1747652).sum := by decide
  have hdescent : baseEnd_1747652 < baseStart_1747652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747663 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 10]
def baseStart_1747663 : Nat := 118140960795 + 1747663 * 2 ^ 59
def prefixEnd_1747663 : Nat := 4983230072969 + 3 ^ 40 * 1747663 * 2
def baseEnd_1747663 : Nat := 398840507146089330744511

theorem tailTrace_1747663 : CollatzResearch.WordTrace tailWord_1747663 prefixEnd_1747663 398840507146089330744511 := by
  unfold tailWord_1747663
  simp only [CollatzResearch.WordTrace]
  refine ⟨63742506267522902922535643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42495004178348601948357095 63742506267522902922535643)
  ·
    refine ⟨95613759401284354383803465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63742506267522902922535643 95613759401284354383803465)
    ·
      refine ⟨71710319550963265787852599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95613759401284354383803465 71710319550963265787852599)
      ·
        refine ⟨107565479326444898681778899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71710319550963265787852599 107565479326444898681778899)
        ·
          refine ⟨161348218989667348022668349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107565479326444898681778899 161348218989667348022668349)
          ·
            refine ⟨60505582121125255508500631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161348218989667348022668349 60505582121125255508500631)
            ·
              refine ⟨90758373181687883262750947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60505582121125255508500631 90758373181687883262750947)
              ·
                refine ⟨136137559772531824894126421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90758373181687883262750947 136137559772531824894126421)
                ·
                  refine ⟨398840507146089330744511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 136137559772531824894126421 398840507146089330744511)
                  ·
                    rfl

theorem cell21_1747663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 10].length) (baseStart_1747663 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1747663 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1747663 prefixEnd_1747663 := by exact prefixLift 1747663
  have htrace : WordTrace (prefixWord ++ tailWord_1747663) baseStart_1747663 baseEnd_1747663 := by
    simpa [prefixWord, tailWord_1747663, baseEnd_1747663] using wordTrace_append hprefix tailTrace_1747663
  have hstable : (prefixWord ++ tailWord_1747663).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747663).length < 2 ^ (prefixWord ++ tailWord_1747663).sum := by decide
  have hdescent : baseEnd_1747663 < baseStart_1747663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747669 : List Nat := [1, 3, 2, 5, 1, 1, 3, 5]
def baseStart_1747669 : Nat := 118140960795 + 1747669 * 2 ^ 59
def prefixEnd_1747669 : Nat := 4983230072969 + 3 ^ 40 * 1747669 * 2
def baseEnd_1747669 : Nat := 132947292142611551214833

theorem tailTrace_1747669 : CollatzResearch.WordTrace tailWord_1747669 prefixEnd_1747669 132947292142611551214833 := by
  unfold tailWord_1747669
  simp only [CollatzResearch.WordTrace]
  refine ⟨63742725105501165947254061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42495150070334110631502707 63742725105501165947254061)
  ·
    refine ⟨23903521914562937230220273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63742725105501165947254061 23903521914562937230220273)
    ·
      refine ⟨17927641435922202922665205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23903521914562937230220273 17927641435922202922665205)
      ·
        refine ⟨1680716384617706523999863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17927641435922202922665205 1680716384617706523999863)
        ·
          refine ⟨2521074576926559785999795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1680716384617706523999863 2521074576926559785999795)
          ·
            refine ⟨3781611865389839678999693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2521074576926559785999795 3781611865389839678999693)
            ·
              refine ⟨1418104449521189879624885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3781611865389839678999693 1418104449521189879624885)
              ·
                refine ⟨132947292142611551214833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1418104449521189879624885 132947292142611551214833)
                ·
                  rfl

theorem cell21_1747669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 5].length) (baseStart_1747669 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1747669 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1747669 prefixEnd_1747669 := by exact prefixLift 1747669
  have htrace : WordTrace (prefixWord ++ tailWord_1747669) baseStart_1747669 baseEnd_1747669 := by
    simpa [prefixWord, tailWord_1747669, baseEnd_1747669] using wordTrace_append hprefix tailTrace_1747669
  have hstable : (prefixWord ++ tailWord_1747669).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747669).length < 2 ^ (prefixWord ++ tailWord_1747669).sum := by decide
  have hdescent : baseEnd_1747669 < baseStart_1747669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747683 : List Nat := [1, 1, 1, 7, 1, 1, 1, 5, 3]
def baseStart_1747683 : Nat := 118140960795 + 1747683 * 2 ^ 59
def prefixEnd_1747683 : Nat := 4983230072969 + 3 ^ 40 * 1747683 * 2
def baseEnd_1747683 : Nat := 398845071418573740411137

theorem tailTrace_1747683 : CollatzResearch.WordTrace tailWord_1747683 prefixEnd_1747683 398845071418573740411137 := by
  unfold tailWord_1747683
  simp only [CollatzResearch.WordTrace]
  refine ⟨63743235727450446338263703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42495490484966964225509135 63743235727450446338263703)
  ·
    refine ⟨95614853591175669507395555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63743235727450446338263703 95614853591175669507395555)
    ·
      refine ⟨143422280386763504261093333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95614853591175669507395555 143422280386763504261093333)
      ·
        refine ⟨3361459696564769631119375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 143422280386763504261093333 3361459696564769631119375)
        ·
          refine ⟨5042189544847154446679063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3361459696564769631119375 5042189544847154446679063)
          ·
            refine ⟨7563284317270731670018595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5042189544847154446679063 7563284317270731670018595)
            ·
              refine ⟨11344926475906097505027893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7563284317270731670018595 11344926475906097505027893)
              ·
                refine ⟨1063586857116196641096365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11344926475906097505027893 1063586857116196641096365)
                ·
                  refine ⟨398845071418573740411137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1063586857116196641096365 398845071418573740411137)
                  ·
                    rfl

theorem cell21_1747683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 5, 3].length) (baseStart_1747683 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1747683 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1747683 prefixEnd_1747683 := by exact prefixLift 1747683
  have htrace : WordTrace (prefixWord ++ tailWord_1747683) baseStart_1747683 baseEnd_1747683 := by
    simpa [prefixWord, tailWord_1747683, baseEnd_1747683] using wordTrace_append hprefix tailTrace_1747683
  have hstable : (prefixWord ++ tailWord_1747683).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747683).length < 2 ^ (prefixWord ++ tailWord_1747683).sum := by decide
  have hdescent : baseEnd_1747683 < baseStart_1747683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747756 : List Nat := [2, 2, 1, 1, 1, 4, 2, 4, 4]
def baseStart_1747756 : Nat := 118140960795 + 1747756 * 2 ^ 59
def prefixEnd_1747756 : Nat := 4983230072969 + 3 ^ 40 * 1747756 * 2
def baseEnd_1747756 : Nat := 398861731013141835694321

theorem tailTrace_1747756 : CollatzResearch.WordTrace tailWord_1747756 prefixEnd_1747756 398861731013141835694321 := by
  unfold tailWord_1747756
  simp only [CollatzResearch.WordTrace]
  refine ⟨31872949128092989902835561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42497265504123986537114081 31872949128092989902835561)
  ·
    refine ⟨23904711846069742427126671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31872949128092989902835561 23904711846069742427126671)
    ·
      refine ⟨35857067769104613640690007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23904711846069742427126671 35857067769104613640690007)
      ·
        refine ⟨53785601653656920461035011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35857067769104613640690007 53785601653656920461035011)
        ·
          refine ⟨80678402480485380691552517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53785601653656920461035011 80678402480485380691552517)
          ·
            refine ⟨15127200465091008879666097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80678402480485380691552517 15127200465091008879666097)
            ·
              refine ⟨11345400348818256659749573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15127200465091008879666097 11345400348818256659749573)
              ·
                refine ⟨2127262565403423123703045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11345400348818256659749573 2127262565403423123703045)
                ·
                  refine ⟨398861731013141835694321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2127262565403423123703045 398861731013141835694321)
                  ·
                    rfl

theorem cell21_1747756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 4].length) (baseStart_1747756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1747756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1747756 prefixEnd_1747756 := by exact prefixLift 1747756
  have htrace : WordTrace (prefixWord ++ tailWord_1747756) baseStart_1747756 baseEnd_1747756 := by
    simpa [prefixWord, tailWord_1747756, baseEnd_1747756] using wordTrace_append hprefix tailTrace_1747756
  have hstable : (prefixWord ++ tailWord_1747756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747756).length < 2 ^ (prefixWord ++ tailWord_1747756).sum := by decide
  have hdescent : baseEnd_1747756 < baseStart_1747756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747810 : List Nat := [3, 3, 2, 1, 4, 1, 2, 2, 3]
def baseStart_1747810 : Nat := 118140960795 + 1747810 * 2 ^ 59
def prefixEnd_1747810 : Nat := 4983230072969 + 3 ^ 40 * 1747810 * 2
def baseEnd_1747810 : Nat := 398874054548849741794211

theorem tailTrace_1747810 : CollatzResearch.WordTrace tailWord_1747810 prefixEnd_1747810 398874054548849741794211 := by
  unfold tailWord_1747810
  simp only [CollatzResearch.WordTrace]
  refine ⟨15936966949497586757034221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42498578531993564685424589 15936966949497586757034221)
  ·
    refine ⟨5976362606061595033887833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15936966949497586757034221 5976362606061595033887833)
    ·
      refine ⟨4482271954546196275415875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5976362606061595033887833 4482271954546196275415875)
      ·
        refine ⟨6723407931819294413123813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4482271954546196275415875 6723407931819294413123813)
        ·
          refine ⟨1260638987216117702460715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6723407931819294413123813 1260638987216117702460715)
          ·
            refine ⟨1890958480824176553691073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1260638987216117702460715 1890958480824176553691073)
            ·
              refine ⟨1418218860618132415268305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1890958480824176553691073 1418218860618132415268305)
              ·
                refine ⟨1063664145463599311451229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1418218860618132415268305 1063664145463599311451229)
                ·
                  refine ⟨398874054548849741794211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1063664145463599311451229 398874054548849741794211)
                  ·
                    rfl

theorem cell21_1747810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_1747810 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1747810 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1747810 prefixEnd_1747810 := by exact prefixLift 1747810
  have htrace : WordTrace (prefixWord ++ tailWord_1747810) baseStart_1747810 baseEnd_1747810 := by
    simpa [prefixWord, tailWord_1747810, baseEnd_1747810] using wordTrace_append hprefix tailTrace_1747810
  have hstable : (prefixWord ++ tailWord_1747810).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747810).length < 2 ^ (prefixWord ++ tailWord_1747810).sum := by decide
  have hdescent : baseEnd_1747810 < baseStart_1747810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1747866 : List Nat := [3, 1, 1, 4, 3, 2, 1, 2, 4]
def baseStart_1747866 : Nat := 118140960795 + 1747866 * 2 ^ 59
def prefixEnd_1747866 : Nat := 4983230072969 + 3 ^ 40 * 1747866 * 2
def baseEnd_1747866 : Nat := 398886834511806088860763

theorem tailTrace_1747866 : CollatzResearch.WordTrace tailWord_1747866 prefixEnd_1747866 398886834511806088860763 := by
  unfold tailWord_1747866
  simp only [CollatzResearch.WordTrace]
  refine ⟨15937477571446867148043863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42499940190524979061450301 15937477571446867148043863)
  ·
    refine ⟨23906216357170300722065795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15937477571446867148043863 23906216357170300722065795)
    ·
      refine ⟨35859324535755451083098693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23906216357170300722065795 35859324535755451083098693)
      ·
        refine ⟨6723623350454147078081005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35859324535755451083098693 6723623350454147078081005)
        ·
          refine ⟨2521358756420305154280377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6723623350454147078081005 2521358756420305154280377)
          ·
            refine ⟨1891019067315228865710283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2521358756420305154280377 1891019067315228865710283)
            ·
              refine ⟨2836528600972843298565425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1891019067315228865710283 2836528600972843298565425)
              ·
                refine ⟨2127396450729632473924069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2836528600972843298565425 2127396450729632473924069)
                ·
                  refine ⟨398886834511806088860763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2127396450729632473924069 398886834511806088860763)
                  ·
                    rfl

theorem cell21_1747866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 2, 4].length) (baseStart_1747866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1747866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1747866 prefixEnd_1747866 := by exact prefixLift 1747866
  have htrace : WordTrace (prefixWord ++ tailWord_1747866) baseStart_1747866 baseEnd_1747866 := by
    simpa [prefixWord, tailWord_1747866, baseEnd_1747866] using wordTrace_append hprefix tailTrace_1747866
  have hstable : (prefixWord ++ tailWord_1747866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1747866).length < 2 ^ (prefixWord ++ tailWord_1747866).sum := by decide
  have hdescent : baseEnd_1747866 < baseStart_1747866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1747866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748046 : List Nat := [4, 1, 1, 1, 1, 3, 1, 6, 3]
def baseStart_1748046 : Nat := 118140960795 + 1748046 * 2 ^ 59
def prefixEnd_1748046 : Nat := 4983230072969 + 3 ^ 40 * 1748046 * 2
def baseEnd_1748046 : Nat := 398927912964165775860395

theorem tailTrace_1748046 : CollatzResearch.WordTrace tailWord_1748046 prefixEnd_1748046 398927912964165775860395 := by
  unfold tailWord_1748046
  simp only [CollatzResearch.WordTrace]
  refine ⟨7969559428141919916715999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42504316950090239555818661 7969559428141919916715999)
  ·
    refine ⟨11954339142212879875073999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7969559428141919916715999 11954339142212879875073999)
    ·
      refine ⟨17931508713319319812610999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11954339142212879875073999 17931508713319319812610999)
      ·
        refine ⟨26897263069978979718916499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17931508713319319812610999 26897263069978979718916499)
        ·
          refine ⟨40345894604968469578374749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26897263069978979718916499 40345894604968469578374749)
          ·
            refine ⟨15129710476863176091890531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40345894604968469578374749 15129710476863176091890531)
            ·
              refine ⟨22694565715294764137835797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15129710476863176091890531 22694565715294764137835797)
              ·
                refine ⟨1063807767904442068961053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22694565715294764137835797 1063807767904442068961053)
                ·
                  refine ⟨398927912964165775860395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1063807767904442068961053 398927912964165775860395)
                  ·
                    rfl

theorem cell21_1748046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 6, 3].length) (baseStart_1748046 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1748046 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1748046 prefixEnd_1748046 := by exact prefixLift 1748046
  have htrace : WordTrace (prefixWord ++ tailWord_1748046) baseStart_1748046 baseEnd_1748046 := by
    simpa [prefixWord, tailWord_1748046, baseEnd_1748046] using wordTrace_append hprefix tailTrace_1748046
  have hstable : (prefixWord ++ tailWord_1748046).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748046).length < 2 ^ (prefixWord ++ tailWord_1748046).sum := by decide
  have hdescent : baseEnd_1748046 < baseStart_1748046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748088 : List Nat := [2, 1, 2, 1, 1, 1, 4, 2, 7]
def baseStart_1748088 : Nat := 118140960795 + 1748088 * 2 ^ 59
def prefixEnd_1748088 : Nat := 4983230072969 + 3 ^ 40 * 1748088 * 2
def baseEnd_1748088 : Nat := 398937497936383036160309

theorem tailTrace_1748088 : CollatzResearch.WordTrace tailWord_1748088 prefixEnd_1748088 398937497936383036160309 := by
  unfold tailWord_1748088
  simp only [CollatzResearch.WordTrace]
  refine ⟨31879003645491600253378459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42505338193988800337837945 31879003645491600253378459)
  ·
    refine ⟨47818505468237400380067689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31879003645491600253378459 47818505468237400380067689)
    ·
      refine ⟨35863879101178050285050767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47818505468237400380067689 35863879101178050285050767)
      ·
        refine ⟨53795818651767075427576151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35863879101178050285050767 53795818651767075427576151)
        ·
          refine ⟨80693727977650613141364227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53795818651767075427576151 80693727977650613141364227)
          ·
            refine ⟨121040591966475919712046341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80693727977650613141364227 121040591966475919712046341)
            ·
              refine ⟨22695110993714234946008689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121040591966475919712046341 22695110993714234946008689)
              ·
                refine ⟨17021333245285676209506517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22695110993714234946008689 17021333245285676209506517)
                ·
                  refine ⟨398937497936383036160309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17021333245285676209506517 398937497936383036160309)
                  ·
                    rfl

theorem cell21_1748088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 7].length) (baseStart_1748088 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1748088 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1748088 prefixEnd_1748088 := by exact prefixLift 1748088
  have htrace : WordTrace (prefixWord ++ tailWord_1748088) baseStart_1748088 baseEnd_1748088 := by
    simpa [prefixWord, tailWord_1748088, baseEnd_1748088] using wordTrace_append hprefix tailTrace_1748088
  have hstable : (prefixWord ++ tailWord_1748088).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748088).length < 2 ^ (prefixWord ++ tailWord_1748088).sum := by decide
  have hdescent : baseEnd_1748088 < baseStart_1748088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748105 : List Nat := [1, 2, 1, 1, 4, 3, 3, 1, 5]
def baseStart_1748105 : Nat := 118140960795 + 1748105 * 2 ^ 59
def prefixEnd_1748105 : Nat := 4983230072969 + 3 ^ 40 * 1748105 * 2
def baseEnd_1748105 : Nat := 398941377567994784376941

theorem tailTrace_1748105 : CollatzResearch.WordTrace tailWord_1748105 prefixEnd_1748105 398941377567994784376941 := by
  unfold tailWord_1748105
  simp only [CollatzResearch.WordTrace]
  refine ⟨63758627331921612410125769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42505751554614408273417179 63758627331921612410125769)
  ·
    refine ⟨47818970498941209307594327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63758627331921612410125769 47818970498941209307594327)
    ·
      refine ⟨71728455748411813961391491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47818970498941209307594327 71728455748411813961391491)
      ·
        refine ⟨107592683622617720942087237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71728455748411813961391491 107592683622617720942087237)
        ·
          refine ⟨20173628179240822676641357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107592683622617720942087237 20173628179240822676641357)
          ·
            refine ⟨7565110567215308503740509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20173628179240822676641357 7565110567215308503740509)
            ·
              refine ⟨2836916462705740688902691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7565110567215308503740509 2836916462705740688902691)
              ·
                refine ⟨4255374694058611033354037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2836916462705740688902691 4255374694058611033354037)
                ·
                  refine ⟨398941377567994784376941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4255374694058611033354037 398941377567994784376941)
                  ·
                    rfl

theorem cell21_1748105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 5].length) (baseStart_1748105 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1748105 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1748105 prefixEnd_1748105 := by exact prefixLift 1748105
  have htrace : WordTrace (prefixWord ++ tailWord_1748105) baseStart_1748105 baseEnd_1748105 := by
    simpa [prefixWord, tailWord_1748105, baseEnd_1748105] using wordTrace_append hprefix tailTrace_1748105
  have hstable : (prefixWord ++ tailWord_1748105).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748105).length < 2 ^ (prefixWord ++ tailWord_1748105).sum := by decide
  have hdescent : baseEnd_1748105 < baseStart_1748105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748156 : List Nat := [2, 2, 2, 3, 2, 3, 2, 2, 3]
def baseStart_1748156 : Nat := 118140960795 + 1748156 * 2 ^ 59
def prefixEnd_1748156 : Nat := 4983230072969 + 3 ^ 40 * 1748156 * 2
def baseEnd_1748156 : Nat := 398953016462830029026837

theorem tailTrace_1748156 : CollatzResearch.WordTrace tailWord_1748156 prefixEnd_1748156 398953016462830029026837 := by
  unfold tailWord_1748156
  simp only [CollatzResearch.WordTrace]
  refine ⟨31880243727368424060116161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42506991636491232080154881 31880243727368424060116161)
  ·
    refine ⟨23910182795526318045087121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31880243727368424060116161 23910182795526318045087121)
    ·
      refine ⟨17932637096644738533815341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23910182795526318045087121 17932637096644738533815341)
      ·
        refine ⟨6724738911241776950180753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17932637096644738533815341 6724738911241776950180753)
        ·
          refine ⟨5043554183431332712635565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6724738911241776950180753 5043554183431332712635565)
          ·
            refine ⟨1891332818786749767238337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5043554183431332712635565 1891332818786749767238337)
            ·
              refine ⟨1418499614090062325428753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1891332818786749767238337 1418499614090062325428753)
              ·
                refine ⟨1063874710567546744071565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1418499614090062325428753 1063874710567546744071565)
                ·
                  refine ⟨398953016462830029026837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1063874710567546744071565 398953016462830029026837)
                  ·
                    rfl

theorem cell21_1748156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 2, 3].length) (baseStart_1748156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1748156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1748156 prefixEnd_1748156 := by exact prefixLift 1748156
  have htrace : WordTrace (prefixWord ++ tailWord_1748156) baseStart_1748156 baseEnd_1748156 := by
    simpa [prefixWord, tailWord_1748156, baseEnd_1748156] using wordTrace_append hprefix tailTrace_1748156
  have hstable : (prefixWord ++ tailWord_1748156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748156).length < 2 ^ (prefixWord ++ tailWord_1748156).sum := by decide
  have hdescent : baseEnd_1748156 < baseStart_1748156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748181 : List Nat := [1, 3, 2, 4, 1, 1, 1, 1, 7]
def baseStart_1748181 : Nat := 118140960795 + 1748181 * 2 ^ 59
def prefixEnd_1748181 : Nat := 4983230072969 + 3 ^ 40 * 1748181 * 2
def baseEnd_1748181 : Nat := 398958721803435541110119

theorem tailTrace_1748181 : CollatzResearch.WordTrace tailWord_1748181 prefixEnd_1748181 398958721803435541110119 := by
  unfold tailWord_1748181
  simp only [CollatzResearch.WordTrace]
  refine ⟨63761399279646277389892397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42507599519764184926594931 63761399279646277389892397)
  ·
    refine ⟨23910524729867354021209649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63761399279646277389892397 23910524729867354021209649)
    ·
      refine ⟨17932893547400515515907237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23910524729867354021209649 17932893547400515515907237)
      ·
        refine ⟨3362417540137596659232607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17932893547400515515907237 3362417540137596659232607)
        ·
          refine ⟨5043626310206394988848911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3362417540137596659232607 5043626310206394988848911)
          ·
            refine ⟨7565439465309592483273367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5043626310206394988848911 7565439465309592483273367)
            ·
              refine ⟨11348159197964388724910051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7565439465309592483273367 11348159197964388724910051)
              ·
                refine ⟨17022238796946583087365077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11348159197964388724910051 17022238796946583087365077)
                ·
                  refine ⟨398958721803435541110119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17022238796946583087365077 398958721803435541110119)
                  ·
                    rfl

theorem cell21_1748181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 7].length) (baseStart_1748181 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1748181 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1748181 prefixEnd_1748181 := by exact prefixLift 1748181
  have htrace : WordTrace (prefixWord ++ tailWord_1748181) baseStart_1748181 baseEnd_1748181 := by
    simpa [prefixWord, tailWord_1748181, baseEnd_1748181] using wordTrace_append hprefix tailTrace_1748181
  have hstable : (prefixWord ++ tailWord_1748181).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748181).length < 2 ^ (prefixWord ++ tailWord_1748181).sum := by decide
  have hdescent : baseEnd_1748181 < baseStart_1748181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748271 : List Nat := [1, 1, 2, 1, 2, 1, 3, 6, 4]
def baseStart_1748271 : Nat := 118140960795 + 1748271 * 2 ^ 59
def prefixEnd_1748271 : Nat := 4983230072969 + 3 ^ 40 * 1748271 * 2
def baseEnd_1748271 : Nat := 398979261029615384609935

theorem tailTrace_1748271 : CollatzResearch.WordTrace tailWord_1748271 prefixEnd_1748271 398979261029615384609935 := by
  unfold tailWord_1748271
  simp only [CollatzResearch.WordTrace]
  refine ⟨63764681849320222760668667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42509787899546815173779111 63764681849320222760668667)
  ·
    refine ⟨95647022773980334141003001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63764681849320222760668667 95647022773980334141003001)
    ·
      refine ⟨71735267080485250605752251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95647022773980334141003001 71735267080485250605752251)
      ·
        refine ⟨107602900620727875908628377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71735267080485250605752251 107602900620727875908628377)
        ·
          refine ⟨80702175465545906931471283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107602900620727875908628377 80702175465545906931471283)
          ·
            refine ⟨121053263198318860397206925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80702175465545906931471283 121053263198318860397206925)
            ·
              refine ⟨45394973699369572648952597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121053263198318860397206925 45394973699369572648952597)
              ·
                refine ⟨2127889392157948717919653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45394973699369572648952597 2127889392157948717919653)
                ·
                  refine ⟨398979261029615384609935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2127889392157948717919653 398979261029615384609935)
                  ·
                    rfl

theorem cell21_1748271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 6, 4].length) (baseStart_1748271 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1748271 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1748271 prefixEnd_1748271 := by exact prefixLift 1748271
  have htrace : WordTrace (prefixWord ++ tailWord_1748271) baseStart_1748271 baseEnd_1748271 := by
    simpa [prefixWord, tailWord_1748271, baseEnd_1748271] using wordTrace_append hprefix tailTrace_1748271
  have hstable : (prefixWord ++ tailWord_1748271).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748271).length < 2 ^ (prefixWord ++ tailWord_1748271).sum := by decide
  have hdescent : baseEnd_1748271 < baseStart_1748271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748274 : List Nat := [3, 2, 1, 1, 4, 3, 1, 1, 5]
def baseStart_1748274 : Nat := 118140960795 + 1748274 * 2 ^ 59
def prefixEnd_1748274 : Nat := 4983230072969 + 3 ^ 40 * 1748274 * 2
def baseEnd_1748274 : Nat := 398979945670488046059929

theorem tailTrace_1748274 : CollatzResearch.WordTrace tailWord_1748274 prefixEnd_1748274 398979945670488046059929 := by
  unfold tailWord_1748274
  simp only [CollatzResearch.WordTrace]
  refine ⟨15941197817077338568256969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42509860845539569515351917 15941197817077338568256969)
  ·
    refine ⟨11955898362808003926192727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15941197817077338568256969 11955898362808003926192727)
    ·
      refine ⟨17933847544212005889289091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11955898362808003926192727 17933847544212005889289091)
      ·
        refine ⟨26900771316318008833933637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17933847544212005889289091 26900771316318008833933637)
        ·
          refine ⟨5043894621809626656362557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26900771316318008833933637 5043894621809626656362557)
          ·
            refine ⟨1891460483178609996135959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5043894621809626656362557 1891460483178609996135959)
            ·
              refine ⟨2837190724767914994203939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1891460483178609996135959 2837190724767914994203939)
              ·
                refine ⟨4255786087151872491305909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2837190724767914994203939 4255786087151872491305909)
                ·
                  refine ⟨398979945670488046059929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4255786087151872491305909 398979945670488046059929)
                  ·
                    rfl

theorem cell21_1748274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_1748274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1748274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1748274 prefixEnd_1748274 := by exact prefixLift 1748274
  have htrace : WordTrace (prefixWord ++ tailWord_1748274) baseStart_1748274 baseEnd_1748274 := by
    simpa [prefixWord, tailWord_1748274, baseEnd_1748274] using wordTrace_append hprefix tailTrace_1748274
  have hstable : (prefixWord ++ tailWord_1748274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748274).length < 2 ^ (prefixWord ++ tailWord_1748274).sum := by decide
  have hdescent : baseEnd_1748274 < baseStart_1748274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748347 : List Nat := [1, 1, 1, 1, 1, 6, 1, 5, 4]
def baseStart_1748347 : Nat := 118140960795 + 1748347 * 2 ^ 59
def prefixEnd_1748347 : Nat := 4983230072969 + 3 ^ 40 * 1748347 * 2
def baseEnd_1748347 : Nat := 398996605265056141343113

theorem tailTrace_1748347 : CollatzResearch.WordTrace tailWord_1748347 prefixEnd_1748347 398996605265056141343113 := by
  unfold tailWord_1748347
  simp only [CollatzResearch.WordTrace]
  refine ⟨63767453797044887740435295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42511635864696591826956863 63767453797044887740435295)
  ·
    refine ⟨95651180695567331610652943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63767453797044887740435295 95651180695567331610652943)
    ·
      refine ⟨143476771043350997415979415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95651180695567331610652943 143476771043350997415979415)
      ·
        refine ⟨215215156565026496123969123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143476771043350997415979415 215215156565026496123969123)
        ·
          refine ⟨322822734847539744185953685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215215156565026496123969123 322822734847539744185953685)
          ·
            refine ⟨15132315695978425508716579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 322822734847539744185953685 15132315695978425508716579)
            ·
              refine ⟨22698473543967638263074869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15132315695978425508716579 22698473543967638263074869)
              ·
                refine ⟨2127981894746966087163269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22698473543967638263074869 2127981894746966087163269)
                ·
                  refine ⟨398996605265056141343113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2127981894746966087163269 398996605265056141343113)
                  ·
                    rfl

theorem cell21_1748347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 5, 4].length) (baseStart_1748347 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1748347 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1748347 prefixEnd_1748347 := by exact prefixLift 1748347
  have htrace : WordTrace (prefixWord ++ tailWord_1748347) baseStart_1748347 baseEnd_1748347 := by
    simpa [prefixWord, tailWord_1748347, baseEnd_1748347] using wordTrace_append hprefix tailTrace_1748347
  have hstable : (prefixWord ++ tailWord_1748347).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748347).length < 2 ^ (prefixWord ++ tailWord_1748347).sum := by decide
  have hdescent : baseEnd_1748347 < baseStart_1748347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748381 : List Nat := [1, 4, 2, 1, 3, 3, 1, 2, 4]
def baseStart_1748381 : Nat := 118140960795 + 1748381 * 2 ^ 59
def prefixEnd_1748381 : Nat := 4983230072969 + 3 ^ 40 * 1748381 * 2
def baseEnd_1748381 : Nat := 399004364528279637776377

theorem tailTrace_1748381 : CollatzResearch.WordTrace tailWord_1748381 prefixEnd_1748381 399004364528279637776377 := by
  unfold tailWord_1748381
  simp only [CollatzResearch.WordTrace]
  refine ⟨63768693878921711547172997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42512462585947807698115331 63768693878921711547172997)
  ·
    refine ⟨11956630102297820915094937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63768693878921711547172997 11956630102297820915094937)
    ·
      refine ⟨8967472576723365686321203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11956630102297820915094937 8967472576723365686321203)
      ·
        refine ⟨13451208865085048529481805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8967472576723365686321203 13451208865085048529481805)
        ·
          refine ⟨5044203324406893198555677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13451208865085048529481805 5044203324406893198555677)
          ·
            refine ⟨1891576246652584949458379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5044203324406893198555677 1891576246652584949458379)
            ·
              refine ⟨2837364369978877424187569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1891576246652584949458379 2837364369978877424187569)
              ·
                refine ⟨2128023277484158068140677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2837364369978877424187569 2128023277484158068140677)
                ·
                  refine ⟨399004364528279637776377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2128023277484158068140677 399004364528279637776377)
                  ·
                    rfl

theorem cell21_1748381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_1748381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1748381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1748381 prefixEnd_1748381 := by exact prefixLift 1748381
  have htrace : WordTrace (prefixWord ++ tailWord_1748381) baseStart_1748381 baseEnd_1748381 := by
    simpa [prefixWord, tailWord_1748381, baseEnd_1748381] using wordTrace_append hprefix tailTrace_1748381
  have hstable : (prefixWord ++ tailWord_1748381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748381).length < 2 ^ (prefixWord ++ tailWord_1748381).sum := by decide
  have hdescent : baseEnd_1748381 < baseStart_1748381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748412 : List Nat := [2, 2, 2, 4, 2, 2, 2, 5]
def baseStart_1748412 : Nat := 118140960795 + 1748412 * 2 ^ 59
def prefixEnd_1748412 : Nat := 4983230072969 + 3 ^ 40 * 1748412 * 2
def baseEnd_1748412 : Nat := 133003813050210157586549

theorem tailTrace_1748412 : CollatzResearch.WordTrace tailWord_1748412 prefixEnd_1748412 133003813050210157586549 := by
  unfold tailWord_1748412
  simp only [CollatzResearch.WordTrace]
  refine ⟨31884912270904701920775745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42513216361206269227700993 31884912270904701920775745)
  ·
    refine ⟨23913684203178526440581809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31884912270904701920775745 23913684203178526440581809)
    ·
      refine ⟨17935263152383894830436357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23913684203178526440581809 17935263152383894830436357)
      ·
        refine ⟨3362861841071980280706817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17935263152383894830436357 3362861841071980280706817)
        ·
          refine ⟨2522146380803985210530113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3362861841071980280706817 2522146380803985210530113)
          ·
            refine ⟨1891609785602988907897585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2522146380803985210530113 1891609785602988907897585)
            ·
              refine ⟨1418707339202241680923189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1891609785602988907897585 1418707339202241680923189)
              ·
                refine ⟨133003813050210157586549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1418707339202241680923189 133003813050210157586549)
                ·
                  rfl

theorem cell21_1748412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 5].length) (baseStart_1748412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1748412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1748412 prefixEnd_1748412 := by exact prefixLift 1748412
  have htrace : WordTrace (prefixWord ++ tailWord_1748412) baseStart_1748412 baseEnd_1748412 := by
    simpa [prefixWord, tailWord_1748412, baseEnd_1748412] using wordTrace_append hprefix tailTrace_1748412
  have hstable : (prefixWord ++ tailWord_1748412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748412).length < 2 ^ (prefixWord ++ tailWord_1748412).sum := by decide
  have hdescent : baseEnd_1748412 < baseStart_1748412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748426 : List Nat := [3, 1, 2, 1, 2, 3, 3, 3, 3]
def baseStart_1748426 : Nat := 118140960795 + 1748426 * 2 ^ 59
def prefixEnd_1748426 : Nat := 4983230072969 + 3 ^ 40 * 1748426 * 2
def baseEnd_1748426 : Nat := 399014634141369559526285

theorem tailTrace_1748426 : CollatzResearch.WordTrace tailWord_1748426 prefixEnd_1748426 399014634141369559526285 := by
  unfold tailWord_1748426
  simp only [CollatzResearch.WordTrace]
  refine ⟨15942583790939671058140283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42513556775839122821707421 15942583790939671058140283)
  ·
    refine ⟨23913875686409506587210425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15942583790939671058140283 23913875686409506587210425)
    ·
      refine ⟨17935406764807129940407819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23913875686409506587210425 17935406764807129940407819)
      ·
        refine ⟨26903110147210694910611729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17935406764807129940407819 26903110147210694910611729)
        ·
          refine ⟨20177332610408021182958797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26903110147210694910611729 20177332610408021182958797)
          ·
            refine ⟨7566499728903007943609549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20177332610408021182958797 7566499728903007943609549)
            ·
              refine ⟨2837437398338627978853581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7566499728903007943609549 2837437398338627978853581)
              ·
                refine ⟨1064039024376985492070093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2837437398338627978853581 1064039024376985492070093)
                ·
                  refine ⟨399014634141369559526285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1064039024376985492070093 399014634141369559526285)
                  ·
                    rfl

theorem cell21_1748426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 3, 3].length) (baseStart_1748426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1748426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1748426 prefixEnd_1748426 := by exact prefixLift 1748426
  have htrace : WordTrace (prefixWord ++ tailWord_1748426) baseStart_1748426 baseEnd_1748426 := by
    simpa [prefixWord, tailWord_1748426, baseEnd_1748426] using wordTrace_append hprefix tailTrace_1748426
  have hstable : (prefixWord ++ tailWord_1748426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748426).length < 2 ^ (prefixWord ++ tailWord_1748426).sum := by decide
  have hdescent : baseEnd_1748426 < baseStart_1748426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748485 : List Nat := [1, 3, 1, 1, 2, 2, 1, 7, 3]
def baseStart_1748485 : Nat := 118140960795 + 1748485 * 2 ^ 59
def prefixEnd_1748485 : Nat := 4983230072969 + 3 ^ 40 * 1748485 * 2
def baseEnd_1748485 : Nat := 399028098745198568042831

theorem tailTrace_1748485 : CollatzResearch.WordTrace tailWord_1748485 prefixEnd_1748485 399028098745198568042831 := by
  unfold tailWord_1748485
  simp only [CollatzResearch.WordTrace]
  refine ⟨63772487070544937308958909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42514991380363291539305939 63772487070544937308958909)
  ·
    refine ⟨23914682651454351490859591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63772487070544937308958909 23914682651454351490859591)
    ·
      refine ⟨35872023977181527236289387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23914682651454351490859591 35872023977181527236289387)
      ·
        refine ⟨53808035965772290854434081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35872023977181527236289387 53808035965772290854434081)
        ·
          refine ⟨40356026974329218140825561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53808035965772290854434081 40356026974329218140825561)
          ·
            refine ⟨30267020230746913605619171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40356026974329218140825561 30267020230746913605619171)
            ·
              refine ⟨45400530346120370408428757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30267020230746913605619171 45400530346120370408428757)
              ·
                refine ⟨1064074929987196181447549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 45400530346120370408428757 1064074929987196181447549)
                ·
                  refine ⟨399028098745198568042831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1064074929987196181447549 399028098745198568042831)
                  ·
                    rfl

theorem cell21_1748485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 7, 3].length) (baseStart_1748485 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1748485 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1748485 prefixEnd_1748485 := by exact prefixLift 1748485
  have htrace : WordTrace (prefixWord ++ tailWord_1748485) baseStart_1748485 baseEnd_1748485 := by
    simpa [prefixWord, tailWord_1748485, baseEnd_1748485] using wordTrace_append hprefix tailTrace_1748485
  have hstable : (prefixWord ++ tailWord_1748485).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748485).length < 2 ^ (prefixWord ++ tailWord_1748485).sum := by decide
  have hdescent : baseEnd_1748485 < baseStart_1748485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748499 : List Nat := [1, 1, 1, 2, 1, 6, 1, 4, 4]
def baseStart_1748499 : Nat := 118140960795 + 1748499 * 2 ^ 59
def prefixEnd_1748499 : Nat := 4983230072969 + 3 ^ 40 * 1748499 * 2
def baseEnd_1748499 : Nat := 399031293735937654809469

theorem tailTrace_1748499 : CollatzResearch.WordTrace tailWord_1748499 prefixEnd_1748499 399031293735937654809469 := by
  unfold tailWord_1748499
  simp only [CollatzResearch.WordTrace]
  refine ⟨63772997692494217699968551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42515331794996145133312367 63772997692494217699968551)
  ·
    refine ⟨95659496538741326549952827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63772997692494217699968551 95659496538741326549952827)
    ·
      refine ⟨143489244808111989824929241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95659496538741326549952827 143489244808111989824929241)
      ·
        refine ⟨107616933606083992368696931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143489244808111989824929241 107616933606083992368696931)
        ·
          refine ⟨161425400409125988553045397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107616933606083992368696931 161425400409125988553045397)
          ·
            refine ⟨7566815644177780713424003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 161425400409125988553045397 7566815644177780713424003)
            ·
              refine ⟨11350223466266671070136005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7566815644177780713424003 11350223466266671070136005)
              ·
                refine ⟨2128166899925000825650501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11350223466266671070136005 2128166899925000825650501)
                ·
                  refine ⟨399031293735937654809469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2128166899925000825650501 399031293735937654809469)
                  ·
                    rfl

theorem cell21_1748499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 4, 4].length) (baseStart_1748499 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1748499 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1748499 prefixEnd_1748499 := by exact prefixLift 1748499
  have htrace : WordTrace (prefixWord ++ tailWord_1748499) baseStart_1748499 baseEnd_1748499 := by
    simpa [prefixWord, tailWord_1748499, baseEnd_1748499] using wordTrace_append hprefix tailTrace_1748499
  have hstable : (prefixWord ++ tailWord_1748499).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748499).length < 2 ^ (prefixWord ++ tailWord_1748499).sum := by decide
  have hdescent : baseEnd_1748499 < baseStart_1748499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748561 : List Nat := [1, 2, 2, 1, 3, 2, 1, 6, 3]
def baseStart_1748561 : Nat := 118140960795 + 1748561 * 2 ^ 59
def prefixEnd_1748561 : Nat := 4983230072969 + 3 ^ 40 * 1748561 * 2
def baseEnd_1748561 : Nat := 399045442980639324776009

theorem tailTrace_1748561 : CollatzResearch.WordTrace tailWord_1748561 prefixEnd_1748561 399045442980639324776009 := by
  unfold tailWord_1748561
  simp only [CollatzResearch.WordTrace]
  refine ⟨63775259018269602288725537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42516839345513068192483691 63775259018269602288725537)
  ·
    refine ⟨47831444263702201716544153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63775259018269602288725537 47831444263702201716544153)
    ·
      refine ⟨35873583197776651287408115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47831444263702201716544153 35873583197776651287408115)
      ·
        refine ⟨53810374796664976931112173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35873583197776651287408115 53810374796664976931112173)
        ·
          refine ⟨20178890548749366349167065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53810374796664976931112173 20178890548749366349167065)
          ·
            refine ⟨15134167911562024761875299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20178890548749366349167065 15134167911562024761875299)
            ·
              refine ⟨22701251867343037142812949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15134167911562024761875299 22701251867343037142812949)
              ·
                refine ⟨1064121181281704866069357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22701251867343037142812949 1064121181281704866069357)
                ·
                  refine ⟨399045442980639324776009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1064121181281704866069357 399045442980639324776009)
                  ·
                    rfl

theorem cell21_1748561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 6, 3].length) (baseStart_1748561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1748561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1748561 prefixEnd_1748561 := by exact prefixLift 1748561
  have htrace : WordTrace (prefixWord ++ tailWord_1748561) baseStart_1748561 baseEnd_1748561 := by
    simpa [prefixWord, tailWord_1748561, baseEnd_1748561] using wordTrace_append hprefix tailTrace_1748561
  have hstable : (prefixWord ++ tailWord_1748561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748561).length < 2 ^ (prefixWord ++ tailWord_1748561).sum := by decide
  have hdescent : baseEnd_1748561 < baseStart_1748561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748626 : List Nat := [3, 2, 3, 1, 3, 2, 2, 1, 4]
def baseStart_1748626 : Nat := 118140960795 + 1748626 * 2 ^ 59
def prefixEnd_1748626 : Nat := 4983230072969 + 3 ^ 40 * 1748626 * 2
def baseEnd_1748626 : Nat := 399060276866213656192543

theorem tailTrace_1748626 : CollatzResearch.WordTrace tailWord_1748626 prefixEnd_1748626 399060276866213656192543 := by
  unfold tailWord_1748626
  simp only [CollatzResearch.WordTrace]
  refine ⟨15944407440758529597460433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42518419842022745593227821 15944407440758529597460433)
  ·
    refine ⟨11958305580568897198095325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15944407440758529597460433 11958305580568897198095325)
    ·
      refine ⟨4484364592713336449285747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11958305580568897198095325 4484364592713336449285747)
      ·
        refine ⟨6726546889070004673928621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4484364592713336449285747 6726546889070004673928621)
        ·
          refine ⟨2522455083401251752723233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6726546889070004673928621 2522455083401251752723233)
          ·
            refine ⟨1891841312550938814542425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2522455083401251752723233 1891841312550938814542425)
            ·
              refine ⟨1418880984413204110906819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1891841312550938814542425 1418880984413204110906819)
              ·
                refine ⟨2128321476619806166360229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1418880984413204110906819 2128321476619806166360229)
                ·
                  refine ⟨399060276866213656192543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2128321476619806166360229 399060276866213656192543)
                  ·
                    rfl

theorem cell21_1748626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_1748626 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1748626 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1748626 prefixEnd_1748626 := by exact prefixLift 1748626
  have htrace : WordTrace (prefixWord ++ tailWord_1748626) baseStart_1748626 baseEnd_1748626 := by
    simpa [prefixWord, tailWord_1748626, baseEnd_1748626] using wordTrace_append hprefix tailTrace_1748626
  have hstable : (prefixWord ++ tailWord_1748626).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748626).length < 2 ^ (prefixWord ++ tailWord_1748626).sum := by decide
  have hdescent : baseEnd_1748626 < baseStart_1748626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748668 : List Nat := [2, 2, 2, 3, 1, 3, 2, 2, 4]
def baseStart_1748668 : Nat := 118140960795 + 1748668 * 2 ^ 59
def prefixEnd_1748668 : Nat := 4983230072969 + 3 ^ 40 * 1748668 * 2
def baseEnd_1748668 : Nat := 399069861838430916492457

theorem tailTrace_1748668 : CollatzResearch.WordTrace tailWord_1748668 prefixEnd_1748668 399069861838430916492457 := by
  unfold tailWord_1748668
  simp only [CollatzResearch.WordTrace]
  refine ⟨31889580814440979781435329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42519441085921306375247105 31889580814440979781435329)
  ·
    refine ⟨23917185610830734836076497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31889580814440979781435329 23917185610830734836076497)
    ·
      refine ⟨17937889208123051127057373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23917185610830734836076497 17937889208123051127057373)
      ·
        refine ⟨6726708453046144172646515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17937889208123051127057373 6726708453046144172646515)
        ·
          refine ⟨10090062679569216258969773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6726708453046144172646515 10090062679569216258969773)
          ·
            refine ⟨3783773504838456097113665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10090062679569216258969773 3783773504838456097113665)
            ·
              refine ⟨2837830128628842072835249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3783773504838456097113665 2837830128628842072835249)
              ·
                refine ⟨2128372596471631554626437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2837830128628842072835249 2128372596471631554626437)
                ·
                  refine ⟨399069861838430916492457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2128372596471631554626437 399069861838430916492457)
                  ·
                    rfl

theorem cell21_1748668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 2, 4].length) (baseStart_1748668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1748668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1748668 prefixEnd_1748668 := by exact prefixLift 1748668
  have htrace : WordTrace (prefixWord ++ tailWord_1748668) baseStart_1748668 baseEnd_1748668 := by
    simpa [prefixWord, tailWord_1748668, baseEnd_1748668] using wordTrace_append hprefix tailTrace_1748668
  have hstable : (prefixWord ++ tailWord_1748668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748668).length < 2 ^ (prefixWord ++ tailWord_1748668).sum := by decide
  have hdescent : baseEnd_1748668 < baseStart_1748668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748674 : List Nat := [3, 5, 1, 2, 2, 1, 1, 6]
def baseStart_1748674 : Nat := 118140960795 + 1748674 * 2 ^ 59
def prefixEnd_1748674 : Nat := 4983230072969 + 3 ^ 40 * 1748674 * 2
def baseEnd_1748674 : Nat := 133023743706725413130815

theorem tailTrace_1748674 : CollatzResearch.WordTrace tailWord_1748674 prefixEnd_1748674 133023743706725413130815 := by
  unfold tailWord_1748674
  simp only [CollatzResearch.WordTrace]
  refine ⟨15944845116715055646897269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42519586977906815058392717 15944845116715055646897269)
  ·
    refine ⟨1494829229692036466896619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15944845116715055646897269 1494829229692036466896619)
    ·
      refine ⟨2242243844538054700344929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1494829229692036466896619 2242243844538054700344929)
      ·
        refine ⟨1681682883403541025258697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2242243844538054700344929 1681682883403541025258697)
        ·
          refine ⟨1261262162552655768944023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1681682883403541025258697 1261262162552655768944023)
          ·
            refine ⟨1891893243828983653416035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1261262162552655768944023 1891893243828983653416035)
            ·
              refine ⟨2837839865743475480124053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1891893243828983653416035 2837839865743475480124053)
              ·
                refine ⟨133023743706725413130815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2837839865743475480124053 133023743706725413130815)
                ·
                  rfl

theorem cell21_1748674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 6].length) (baseStart_1748674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1748674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1748674 prefixEnd_1748674 := by exact prefixLift 1748674
  have htrace : WordTrace (prefixWord ++ tailWord_1748674) baseStart_1748674 baseEnd_1748674 := by
    simpa [prefixWord, tailWord_1748674, baseEnd_1748674] using wordTrace_append hprefix tailTrace_1748674
  have hstable : (prefixWord ++ tailWord_1748674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748674).length < 2 ^ (prefixWord ++ tailWord_1748674).sum := by decide
  have hdescent : baseEnd_1748674 < baseStart_1748674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748685 : List Nat := [1, 6, 2, 1, 1, 1, 2, 3, 4]
def baseStart_1748685 : Nat := 118140960795 + 1748685 * 2 ^ 59
def prefixEnd_1748685 : Nat := 4983230072969 + 3 ^ 40 * 1748685 * 2
def baseEnd_1748685 : Nat := 399073741470042664709089

theorem tailTrace_1748685 : CollatzResearch.WordTrace tailWord_1748685 prefixEnd_1748685 399073741470042664709089 := by
  unfold tailWord_1748685
  simp only [CollatzResearch.WordTrace]
  refine ⟨63779781669820371466239509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42519854446546914310826339 63779781669820371466239509)
  ·
    refine ⟨2989677265772829912479977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 63779781669820371466239509 2989677265772829912479977)
    ·
      refine ⟨2242257949329622434359983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2989677265772829912479977 2242257949329622434359983)
      ·
        refine ⟨3363386923994433651539975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2242257949329622434359983 3363386923994433651539975)
        ·
          refine ⟨5045080385991650477309963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3363386923994433651539975 5045080385991650477309963)
          ·
            refine ⟨7567620578987475715964945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5045080385991650477309963 7567620578987475715964945)
            ·
              refine ⟨5675715434240606786973709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7567620578987475715964945 5675715434240606786973709)
              ·
                refine ⟨2128393287840227545115141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5675715434240606786973709 2128393287840227545115141)
                ·
                  refine ⟨399073741470042664709089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2128393287840227545115141 399073741470042664709089)
                  ·
                    rfl

theorem cell21_1748685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_1748685 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1748685 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1748685 prefixEnd_1748685 := by exact prefixLift 1748685
  have htrace : WordTrace (prefixWord ++ tailWord_1748685) baseStart_1748685 baseEnd_1748685 := by
    simpa [prefixWord, tailWord_1748685, baseEnd_1748685] using wordTrace_append hprefix tailTrace_1748685
  have hstable : (prefixWord ++ tailWord_1748685).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748685).length < 2 ^ (prefixWord ++ tailWord_1748685).sum := by decide
  have hdescent : baseEnd_1748685 < baseStart_1748685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748696 : List Nat := [2, 1, 2, 2, 3, 1, 3, 2, 5]
def baseStart_1748696 : Nat := 118140960795 + 1748696 * 2 ^ 59
def prefixEnd_1748696 : Nat := 4983230072969 + 3 ^ 40 * 1748696 * 2
def baseEnd_1748696 : Nat := 399076251819909090025733

theorem tailTrace_1748696 : CollatzResearch.WordTrace tailWord_1748696 prefixEnd_1748696 399076251819909090025733 := by
  unfold tailWord_1748696
  simp only [CollatzResearch.WordTrace]
  refine ⟨31890091436390260172444971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42520121915187013563259961 31890091436390260172444971)
  ·
    refine ⟨47835137154585390258667457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31890091436390260172444971 47835137154585390258667457)
    ·
      refine ⟨35876352865939042694000593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47835137154585390258667457 35876352865939042694000593)
      ·
        refine ⟨26907264649454282020500445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35876352865939042694000593 26907264649454282020500445)
        ·
          refine ⟨10090224243545355757687667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26907264649454282020500445 10090224243545355757687667)
          ·
            refine ⟨15135336365318033636531501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10090224243545355757687667 15135336365318033636531501)
            ·
              refine ⟨5675751136994262613699313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15135336365318033636531501 5675751136994262613699313)
              ·
                refine ⟨4256813352745696960274485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5675751136994262613699313 4256813352745696960274485)
                ·
                  refine ⟨399076251819909090025733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4256813352745696960274485 399076251819909090025733)
                  ·
                    rfl

theorem cell21_1748696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 5].length) (baseStart_1748696 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1748696 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1748696 prefixEnd_1748696 := by exact prefixLift 1748696
  have htrace : WordTrace (prefixWord ++ tailWord_1748696) baseStart_1748696 baseEnd_1748696 := by
    simpa [prefixWord, tailWord_1748696, baseEnd_1748696] using wordTrace_append hprefix tailTrace_1748696
  have hstable : (prefixWord ++ tailWord_1748696).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748696).length < 2 ^ (prefixWord ++ tailWord_1748696).sum := by decide
  have hdescent : baseEnd_1748696 < baseStart_1748696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748727 : List Nat := [1, 1, 3, 1, 1, 1, 7, 2, 4]
def baseStart_1748727 : Nat := 118140960795 + 1748727 * 2 ^ 59
def prefixEnd_1748727 : Nat := 4983230072969 + 3 ^ 40 * 1748727 * 2
def baseEnd_1748727 : Nat := 399083326442259925009003

theorem tailTrace_1748727 : CollatzResearch.WordTrace tailWord_1748727 prefixEnd_1748727 399083326442259925009003 := by
  unfold tailWord_1748727
  simp only [CollatzResearch.WordTrace]
  refine ⟨63781313535668212639268435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42520875690445475092845623 63781313535668212639268435)
  ·
    refine ⟨95671970303502318958902653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63781313535668212639268435 95671970303502318958902653)
    ·
      refine ⟨35876988863813369609588495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95671970303502318958902653 35876988863813369609588495)
      ·
        refine ⟨53815483295720054414382743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35876988863813369609588495 53815483295720054414382743)
        ·
          refine ⟨80723224943580081621574115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53815483295720054414382743 80723224943580081621574115)
          ·
            refine ⟨121084837415370122432361173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80723224943580081621574115 121084837415370122432361173)
            ·
              refine ⟨2837925876922737244508465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 121084837415370122432361173 2837925876922737244508465)
              ·
                refine ⟨2128444407692052933381349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2837925876922737244508465 2128444407692052933381349)
                ·
                  refine ⟨399083326442259925009003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2128444407692052933381349 399083326442259925009003)
                  ·
                    rfl

theorem cell21_1748727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 2, 4].length) (baseStart_1748727 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1748727 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1748727 prefixEnd_1748727 := by exact prefixLift 1748727
  have htrace : WordTrace (prefixWord ++ tailWord_1748727) baseStart_1748727 baseEnd_1748727 := by
    simpa [prefixWord, tailWord_1748727, baseEnd_1748727] using wordTrace_append hprefix tailTrace_1748727
  have hstable : (prefixWord ++ tailWord_1748727).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748727).length < 2 ^ (prefixWord ++ tailWord_1748727).sum := by decide
  have hdescent : baseEnd_1748727 < baseStart_1748727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748744 : List Nat := [2, 1, 3, 2, 2, 1, 5, 1, 4]
def baseStart_1748744 : Nat := 118140960795 + 1748744 * 2 ^ 59
def prefixEnd_1748744 : Nat := 4983230072969 + 3 ^ 40 * 1748744 * 2
def baseEnd_1748744 : Nat := 399087206073871673225635

theorem tailTrace_1748744 : CollatzResearch.WordTrace tailWord_1748744 prefixEnd_1748744 399087206073871673225635 := by
  unfold tailWord_1748744
  simp only [CollatzResearch.WordTrace]
  refine ⟨31890966788303312271318643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42521289051071083028424857 31890966788303312271318643)
  ·
    refine ⟨47836450182454968406977965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31890966788303312271318643 47836450182454968406977965)
    ·
      refine ⟨17938668818420613152616737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47836450182454968406977965 17938668818420613152616737)
      ·
        refine ⟨13454001613815459864462553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17938668818420613152616737 13454001613815459864462553)
        ·
          refine ⟨10090501210361594898346915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13454001613815459864462553 10090501210361594898346915)
          ·
            refine ⟨15135751815542392347520373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10090501210361594898346915 15135751815542392347520373)
            ·
              refine ⟨1418976732707099282580035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15135751815542392347520373 1418976732707099282580035)
              ·
                refine ⟨2128465099060648923870053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1418976732707099282580035 2128465099060648923870053)
                ·
                  refine ⟨399087206073871673225635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2128465099060648923870053 399087206073871673225635)
                  ·
                    rfl

theorem cell21_1748744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 1, 4].length) (baseStart_1748744 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1748744 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1748744 prefixEnd_1748744 := by exact prefixLift 1748744
  have htrace : WordTrace (prefixWord ++ tailWord_1748744) baseStart_1748744 baseEnd_1748744 := by
    simpa [prefixWord, tailWord_1748744, baseEnd_1748744] using wordTrace_append hprefix tailTrace_1748744
  have hstable : (prefixWord ++ tailWord_1748744).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748744).length < 2 ^ (prefixWord ++ tailWord_1748744).sum := by decide
  have hdescent : baseEnd_1748744 < baseStart_1748744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748755 : List Nat := [1, 1, 1, 2, 1, 3, 2, 3, 7]
def baseStart_1748755 : Nat := 118140960795 + 1748755 * 2 ^ 59
def prefixEnd_1748755 : Nat := 4983230072969 + 3 ^ 40 * 1748755 * 2
def baseEnd_1748755 : Nat := 399089716423738098542279

theorem tailTrace_1748755 : CollatzResearch.WordTrace tailWord_1748755 prefixEnd_1748755 399089716423738098542279 := by
  unfold tailWord_1748755
  simp only [CollatzResearch.WordTrace]
  refine ⟨63782334779566773421287719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42521556519711182280858479 63782334779566773421287719)
  ·
    refine ⟨95673502169350160131931579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63782334779566773421287719 95673502169350160131931579)
    ·
      refine ⟨143510253254025240197897369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95673502169350160131931579 143510253254025240197897369)
      ·
        refine ⟨107632689940518930148423027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143510253254025240197897369 107632689940518930148423027)
        ·
          refine ⟨161449034910778395222634541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107632689940518930148423027 161449034910778395222634541)
          ·
            refine ⟨60543388091541898208487953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161449034910778395222634541 60543388091541898208487953)
            ·
              refine ⟨45407541068656423656365965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60543388091541898208487953 45407541068656423656365965)
              ·
                refine ⟨17027827900746158871137237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45407541068656423656365965 17027827900746158871137237)
                ·
                  refine ⟨399089716423738098542279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17027827900746158871137237 399089716423738098542279)
                  ·
                    rfl

theorem cell21_1748755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 7].length) (baseStart_1748755 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1748755 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1748755 prefixEnd_1748755 := by exact prefixLift 1748755
  have htrace : WordTrace (prefixWord ++ tailWord_1748755) baseStart_1748755 baseEnd_1748755 := by
    simpa [prefixWord, tailWord_1748755, baseEnd_1748755] using wordTrace_append hprefix tailTrace_1748755
  have hstable : (prefixWord ++ tailWord_1748755).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748755).length < 2 ^ (prefixWord ++ tailWord_1748755).sum := by decide
  have hdescent : baseEnd_1748755 < baseStart_1748755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748803 : List Nat := [1, 1, 1, 3, 1, 6, 1, 3, 4]
def baseStart_1748803 : Nat := 118140960795 + 1748803 * 2 ^ 59
def prefixEnd_1748803 : Nat := 4983230072969 + 3 ^ 40 * 1748803 * 2
def baseEnd_1748803 : Nat := 399100670677700681742181

theorem tailTrace_1748803 : CollatzResearch.WordTrace tailWord_1748803 prefixEnd_1748803 399100670677700681742181 := by
  unfold tailWord_1748803
  simp only [CollatzResearch.WordTrace]
  refine ⟨63784085483392877619035063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42522723655595251746023375 63784085483392877619035063)
  ·
    refine ⟨95676128225089316428552595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63784085483392877619035063 95676128225089316428552595)
    ·
      refine ⟨143514192337633974642828893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95676128225089316428552595 143514192337633974642828893)
      ·
        refine ⟨53817822126612740491060835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143514192337633974642828893 53817822126612740491060835)
        ·
          refine ⟨80726733189919110736591253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53817822126612740491060835 80726733189919110736591253)
          ·
            refine ⟨3784065618277458315777715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 80726733189919110736591253 3784065618277458315777715)
            ·
              refine ⟨5676098427416187473666573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3784065618277458315777715 5676098427416187473666573)
              ·
                refine ⟨2128536910281070302624965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5676098427416187473666573 2128536910281070302624965)
                ·
                  refine ⟨399100670677700681742181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2128536910281070302624965 399100670677700681742181)
                  ·
                    rfl

theorem cell21_1748803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 3, 4].length) (baseStart_1748803 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1748803 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1748803 prefixEnd_1748803 := by exact prefixLift 1748803
  have htrace : WordTrace (prefixWord ++ tailWord_1748803) baseStart_1748803 baseEnd_1748803 := by
    simpa [prefixWord, tailWord_1748803, baseEnd_1748803] using wordTrace_append hprefix tailTrace_1748803
  have hstable : (prefixWord ++ tailWord_1748803).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748803).length < 2 ^ (prefixWord ++ tailWord_1748803).sum := by decide
  have hdescent : baseEnd_1748803 < baseStart_1748803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748817 : List Nat := [1, 2, 2, 1, 5, 1, 2, 7]
def baseStart_1748817 : Nat := 118140960795 + 1748817 * 2 ^ 59
def prefixEnd_1748817 : Nat := 4983230072969 + 3 ^ 40 * 1748817 * 2
def baseEnd_1748817 : Nat := 133034621889479922836273

theorem tailTrace_1748817 : CollatzResearch.WordTrace tailWord_1748817 prefixEnd_1748817 133034621889479922836273 := by
  unfold tailWord_1748817
  simp only [CollatzResearch.WordTrace]
  refine ⟨63784596105342158010044705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42523064070228105340029803 63784596105342158010044705)
  ·
    refine ⟨47838447079006618507533529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63784596105342158010044705 47838447079006618507533529)
    ·
      refine ⟨35878835309254963880650147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47838447079006618507533529 35878835309254963880650147)
      ·
        refine ⟨53818252963882445820975221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35878835309254963880650147 53818252963882445820975221)
        ·
          refine ⟨5045461215363979295716427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53818252963882445820975221 5045461215363979295716427)
          ·
            refine ⟨7568191823045968943574641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5045461215363979295716427 7568191823045968943574641)
            ·
              refine ⟨5676143867284476707680981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7568191823045968943574641 5676143867284476707680981)
              ·
                refine ⟨133034621889479922836273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5676143867284476707680981 133034621889479922836273)
                ·
                  rfl

theorem cell21_1748817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 7].length) (baseStart_1748817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1748817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1748817 prefixEnd_1748817 := by exact prefixLift 1748817
  have htrace : WordTrace (prefixWord ++ tailWord_1748817) baseStart_1748817 baseEnd_1748817 := by
    simpa [prefixWord, tailWord_1748817, baseEnd_1748817] using wordTrace_append hprefix tailTrace_1748817
  have hstable : (prefixWord ++ tailWord_1748817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748817).length < 2 ^ (prefixWord ++ tailWord_1748817).sum := by decide
  have hdescent : baseEnd_1748817 < baseStart_1748817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748882 : List Nat := [3, 2, 3, 2, 1, 1, 1, 5, 3]
def baseStart_1748882 : Nat := 118140960795 + 1748882 * 2 ^ 59
def prefixEnd_1748882 : Nat := 4983230072969 + 3 ^ 40 * 1748882 * 2
def baseEnd_1748882 : Nat := 399118699554014099925353

theorem tailTrace_1748882 : CollatzResearch.WordTrace tailWord_1748882 prefixEnd_1748882 399118699554014099925353 := by
  unfold tailWord_1748882
  simp only [CollatzResearch.WordTrace]
  refine ⟨15946741712526668527790225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42524644566737782740773933 15946741712526668527790225)
  ·
    refine ⟨11960056284395001395842669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15946741712526668527790225 11960056284395001395842669)
    ·
      refine ⟨4485021106648125523441001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11960056284395001395842669 4485021106648125523441001)
      ·
        refine ⟨3363765829986094142580751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4485021106648125523441001 3363765829986094142580751)
        ·
          refine ⟨5045648744979141213871127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3363765829986094142580751 5045648744979141213871127)
          ·
            refine ⟨7568473117468711820806691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5045648744979141213871127 7568473117468711820806691)
            ·
              refine ⟨11352709676203067731210037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7568473117468711820806691 11352709676203067731210037)
              ·
                refine ⟨1064316532144037599800941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11352709676203067731210037 1064316532144037599800941)
                ·
                  refine ⟨399118699554014099925353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1064316532144037599800941 399118699554014099925353)
                  ·
                    rfl

theorem cell21_1748882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 5, 3].length) (baseStart_1748882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1748882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1748882 prefixEnd_1748882 := by exact prefixLift 1748882
  have htrace : WordTrace (prefixWord ++ tailWord_1748882) baseStart_1748882 baseEnd_1748882 := by
    simpa [prefixWord, tailWord_1748882, baseEnd_1748882] using wordTrace_append hprefix tailTrace_1748882
  have hstable : (prefixWord ++ tailWord_1748882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748882).length < 2 ^ (prefixWord ++ tailWord_1748882).sum := by decide
  have hdescent : baseEnd_1748882 < baseStart_1748882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748893 : List Nat := [1, 4, 2, 1, 2, 3, 8]
def baseStart_1748893 : Nat := 118140960795 + 1748893 * 2 ^ 59
def prefixEnd_1748893 : Nat := 4983230072969 + 3 ^ 40 * 1748893 * 2
def baseEnd_1748893 : Nat := 44346801100431169471333

theorem tailTrace_1748893 : CollatzResearch.WordTrace tailWord_1748893 prefixEnd_1748893 44346801100431169471333 := by
  unfold tailWord_1748893
  simp only [CollatzResearch.WordTrace]
  refine ⟨63787368053066822989811333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42524912035377881993207555 63787368053066822989811333)
  ·
    refine ⟨11960131509950029310589625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63787368053066822989811333 11960131509950029310589625)
    ·
      refine ⟨8970098632462521982942219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11960131509950029310589625 8970098632462521982942219)
      ·
        refine ⟨13455147948693782974413329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8970098632462521982942219 13455147948693782974413329)
        ·
          refine ⟨10091360961520337230809997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13455147948693782974413329 10091360961520337230809997)
          ·
            refine ⟨3784260360570126461553749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10091360961520337230809997 3784260360570126461553749)
            ·
              refine ⟨44346801100431169471333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3784260360570126461553749 44346801100431169471333)
              ·
                rfl

theorem cell21_1748893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 8].length) (baseStart_1748893 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1748893 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1748893 prefixEnd_1748893 := by exact prefixLift 1748893
  have htrace : WordTrace (prefixWord ++ tailWord_1748893) baseStart_1748893 baseEnd_1748893 := by
    simpa [prefixWord, tailWord_1748893, baseEnd_1748893] using wordTrace_append hprefix tailTrace_1748893
  have hstable : (prefixWord ++ tailWord_1748893).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748893).length < 2 ^ (prefixWord ++ tailWord_1748893).sum := by decide
  have hdescent : baseEnd_1748893 < baseStart_1748893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1748938 : List Nat := [3, 1, 2, 1, 2, 1, 3, 2, 6]
def baseStart_1748938 : Nat := 118140960795 + 1748938 * 2 ^ 59
def prefixEnd_1748938 : Nat := 4983230072969 + 3 ^ 40 * 1748938 * 2
def baseEnd_1748938 : Nat := 399131479516970446991905

theorem tailTrace_1748938 : CollatzResearch.WordTrace tailWord_1748938 prefixEnd_1748938 399131479516970446991905 := by
  unfold tailWord_1748938
  simp only [CollatzResearch.WordTrace]
  refine ⟨15947252334475948918799867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42526006225269197116799645 15947252334475948918799867)
  ·
    refine ⟨23920878501713923378199801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15947252334475948918799867 23920878501713923378199801)
    ·
      refine ⟨17940658876285442533649851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23920878501713923378199801 17940658876285442533649851)
      ·
        refine ⟨26910988314428163800474777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17940658876285442533649851 26910988314428163800474777)
        ·
          refine ⟨20183241235821122850356083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26910988314428163800474777 20183241235821122850356083)
          ·
            refine ⟨30274861853731684275534125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20183241235821122850356083 30274861853731684275534125)
            ·
              refine ⟨11353073195149381603325297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30274861853731684275534125 11353073195149381603325297)
              ·
                refine ⟨8514804896362036202493973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11353073195149381603325297 8514804896362036202493973)
                ·
                  refine ⟨399131479516970446991905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8514804896362036202493973 399131479516970446991905)
                  ·
                    rfl

theorem cell21_1748938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 6].length) (baseStart_1748938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1748938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1748938 prefixEnd_1748938 := by exact prefixLift 1748938
  have htrace : WordTrace (prefixWord ++ tailWord_1748938) baseStart_1748938 baseEnd_1748938 := by
    simpa [prefixWord, tailWord_1748938, baseEnd_1748938] using wordTrace_append hprefix tailTrace_1748938
  have hstable : (prefixWord ++ tailWord_1748938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1748938).length < 2 ^ (prefixWord ++ tailWord_1748938).sum := by decide
  have hdescent : baseEnd_1748938 < baseStart_1748938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1748938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749062 : List Nat := [6, 1, 1, 1, 1, 1, 10]
def baseStart_1749062 : Nat := 118140960795 + 1749062 * 2 ^ 59
def prefixEnd_1749062 : Nat := 4983230072969 + 3 ^ 40 * 1749062 * 2
def baseEnd_1749062 : Nat := 44351086445152642991665

theorem tailTrace_1749062 : CollatzResearch.WordTrace tailWord_1749062 prefixEnd_1749062 44351086445152642991665 := by
  unfold tailWord_1749062
  simp only [CollatzResearch.WordTrace]
  refine ⟨1993547874670455151647295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 42529021326303043235142293 1993547874670455151647295)
  ·
    refine ⟨2990321812005682727470943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1993547874670455151647295 2990321812005682727470943)
    ·
      refine ⟨4485482718008524091206415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2990321812005682727470943 4485482718008524091206415)
      ·
        refine ⟨6728224077012786136809623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4485482718008524091206415 6728224077012786136809623)
        ·
          refine ⟨10092336115519179205214435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6728224077012786136809623 10092336115519179205214435)
          ·
            refine ⟨15138504173278768807821653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10092336115519179205214435 15138504173278768807821653)
            ·
              refine ⟨44351086445152642991665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15138504173278768807821653 44351086445152642991665)
              ·
                rfl

theorem cell21_1749062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 10].length) (baseStart_1749062 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1749062 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1749062 prefixEnd_1749062 := by exact prefixLift 1749062
  have htrace : WordTrace (prefixWord ++ tailWord_1749062) baseStart_1749062 baseEnd_1749062 := by
    simpa [prefixWord, tailWord_1749062, baseEnd_1749062] using wordTrace_append hprefix tailTrace_1749062
  have hstable : (prefixWord ++ tailWord_1749062).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749062).length < 2 ^ (prefixWord ++ tailWord_1749062).sum := by decide
  have hdescent : baseEnd_1749062 < baseStart_1749062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749110 : List Nat := [5, 1, 1, 2, 1, 2, 3, 3, 3]
def baseStart_1749110 : Nat := 118140960795 + 1749110 * 2 ^ 59
def prefixEnd_1749110 : Nat := 4983230072969 + 3 ^ 40 * 1749110 * 2
def baseEnd_1749110 : Nat := 399170732260336370124887

theorem tailTrace_1749110 : CollatzResearch.WordTrace tailWord_1749110 prefixEnd_1749110 399170732260336370124887 := by
  unfold tailWord_1749110
  simp only [CollatzResearch.WordTrace]
  refine ⟨3987205168330041815653799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42530188462187112700307189 3987205168330041815653799)
  ·
    refine ⟨5980807752495062723480699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3987205168330041815653799 5980807752495062723480699)
    ·
      refine ⟨8971211628742594085221049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5980807752495062723480699 8971211628742594085221049)
      ·
        refine ⟨6728408721556945563915787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8971211628742594085221049 6728408721556945563915787)
        ·
          refine ⟨10092613082335418345873681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6728408721556945563915787 10092613082335418345873681)
          ·
            refine ⟨7569459811751563759405261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10092613082335418345873681 7569459811751563759405261)
            ·
              refine ⟨2838547429406836409776973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7569459811751563759405261 2838547429406836409776973)
              ·
                refine ⟨1064455286027563653666365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2838547429406836409776973 1064455286027563653666365)
                ·
                  refine ⟨399170732260336370124887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1064455286027563653666365 399170732260336370124887)
                  ·
                    rfl

theorem cell21_1749110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_1749110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1749110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1749110 prefixEnd_1749110 := by exact prefixLift 1749110
  have htrace : WordTrace (prefixWord ++ tailWord_1749110) baseStart_1749110 baseEnd_1749110 := by
    simpa [prefixWord, tailWord_1749110, baseEnd_1749110] using wordTrace_append hprefix tailTrace_1749110
  have hstable : (prefixWord ++ tailWord_1749110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749110).length < 2 ^ (prefixWord ++ tailWord_1749110).sum := by decide
  have hdescent : baseEnd_1749110 < baseStart_1749110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749172 : List Nat := [2, 5, 3, 1, 2, 8]
def baseStart_1749172 : Nat := 118140960795 + 1749172 * 2 ^ 59
def prefixEnd_1749172 : Nat := 4983230072969 + 3 ^ 40 * 1749172 * 2
def baseEnd_1749172 : Nat := 14784625240927334818201

theorem tailTrace_1749172 : CollatzResearch.WordTrace tailWord_1749172 prefixEnd_1749172 14784625240927334818201 := by
  unfold tailWord_1749172
  simp only [CollatzResearch.WordTrace]
  refine ⟨31898772009528026819608885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42531696012704035759478513 31898772009528026819608885)
  ·
    refine ⟨2990509875893252514338333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31898772009528026819608885 2990509875893252514338333)
    ·
      refine ⟨1121441203459969692876875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2990509875893252514338333 1121441203459969692876875)
      ·
        refine ⟨1682161805189954539315313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1121441203459969692876875 1682161805189954539315313)
        ·
          refine ⟨1261621353892465904486485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1682161805189954539315313 1261621353892465904486485)
          ·
            refine ⟨14784625240927334818201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1261621353892465904486485 14784625240927334818201)
            ·
              rfl

theorem cell21_1749172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 8].length) (baseStart_1749172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1749172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1749172 prefixEnd_1749172 := by exact prefixLift 1749172
  have htrace : WordTrace (prefixWord ++ tailWord_1749172) baseStart_1749172 baseEnd_1749172 := by
    simpa [prefixWord, tailWord_1749172, baseEnd_1749172] using wordTrace_append hprefix tailTrace_1749172
  have hstable : (prefixWord ++ tailWord_1749172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749172).length < 2 ^ (prefixWord ++ tailWord_1749172).sum := by decide
  have hdescent : baseEnd_1749172 < baseStart_1749172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749180 : List Nat := [2, 2, 2, 3, 12]
def baseStart_1749180 : Nat := 118140960795 + 1749180 * 2 ^ 59
def prefixEnd_1749180 : Nat := 4983230072969 + 3 ^ 40 * 1749180 * 2
def baseEnd_1749180 : Nat := 4928230953259651900717

theorem tailTrace_1749180 : CollatzResearch.WordTrace tailWord_1749180 prefixEnd_1749180 4928230953259651900717 := by
  unfold tailWord_1749180
  simp only [CollatzResearch.WordTrace]
  refine ⟨31898917901513535502754497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42531890535351380670339329 31898917901513535502754497)
  ·
    refine ⟨23924188426135151627065873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31898917901513535502754497 23924188426135151627065873)
    ·
      refine ⟨17943141319601363720299405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23924188426135151627065873 17943141319601363720299405)
      ·
        refine ⟨6728677994850511395112277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17943141319601363720299405 6728677994850511395112277)
        ·
          refine ⟨4928230953259651900717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 6728677994850511395112277 4928230953259651900717)
          ·
            rfl

theorem cell21_1749180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 12].length) (baseStart_1749180 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1749180 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1749180 prefixEnd_1749180 := by exact prefixLift 1749180
  have htrace : WordTrace (prefixWord ++ tailWord_1749180) baseStart_1749180 baseEnd_1749180 := by
    simpa [prefixWord, tailWord_1749180, baseEnd_1749180] using wordTrace_append hprefix tailTrace_1749180
  have hstable : (prefixWord ++ tailWord_1749180).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749180).length < 2 ^ (prefixWord ++ tailWord_1749180).sum := by decide
  have hdescent : baseEnd_1749180 < baseStart_1749180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749225 : List Nat := [1, 2, 1, 1, 1, 2, 2, 3, 8]
def baseStart_1749225 : Nat := 118140960795 + 1749225 * 2 ^ 59
def prefixEnd_1749225 : Nat := 4983230072969 + 3 ^ 40 * 1749225 * 2
def baseEnd_1749225 : Nat := 399196976827121725707985

theorem tailTrace_1749225 : CollatzResearch.WordTrace tailWord_1749225 prefixEnd_1749225 399196976827121725707985 := by
  unfold tailWord_1749225
  simp only [CollatzResearch.WordTrace]
  refine ⟨63799477087864043690897129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42532984725242695793931419 63799477087864043690897129)
  ·
    refine ⟨47849607815898032768172847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63799477087864043690897129 47849607815898032768172847)
    ·
      refine ⟨71774411723847049152259271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47849607815898032768172847 71774411723847049152259271)
      ·
        refine ⟨107661617585770573728388907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71774411723847049152259271 107661617585770573728388907)
        ·
          refine ⟨161492426378655860592583361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107661617585770573728388907 161492426378655860592583361)
          ·
            refine ⟨121119319783991895444437521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161492426378655860592583361 121119319783991895444437521)
            ·
              refine ⟨90839489837993921583328141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121119319783991895444437521 90839489837993921583328141)
              ·
                refine ⟨34064808689247720593748053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90839489837993921583328141 34064808689247720593748053)
                ·
                  refine ⟨399196976827121725707985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34064808689247720593748053 399196976827121725707985)
                  ·
                    rfl

theorem cell21_1749225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 8].length) (baseStart_1749225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1749225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1749225 prefixEnd_1749225 := by exact prefixLift 1749225
  have htrace : WordTrace (prefixWord ++ tailWord_1749225) baseStart_1749225 baseEnd_1749225 := by
    simpa [prefixWord, tailWord_1749225, baseEnd_1749225] using wordTrace_append hprefix tailTrace_1749225
  have hstable : (prefixWord ++ tailWord_1749225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749225).length < 2 ^ (prefixWord ++ tailWord_1749225).sum := by decide
  have hdescent : baseEnd_1749225 < baseStart_1749225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749242 : List Nat := [3, 1, 1, 1, 1, 6, 1, 1, 6]
def baseStart_1749242 : Nat := 118140960795 + 1749242 * 2 ^ 59
def prefixEnd_1749242 : Nat := 4983230072969 + 3 ^ 40 * 1749242 * 2
def baseEnd_1749242 : Nat := 399200856458733473924617

theorem tailTrace_1749242 : CollatzResearch.WordTrace tailWord_1749242 prefixEnd_1749242 399200856458733473924617 := by
  unfold tailWord_1749242
  simp only [CollatzResearch.WordTrace]
  refine ⟨15950024282200613898566495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42533398085868303729510653 15950024282200613898566495)
  ·
    refine ⟨23925036423300920847849743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15950024282200613898566495 23925036423300920847849743)
    ·
      refine ⟨35887554634951381271774615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23925036423300920847849743 35887554634951381271774615)
      ·
        refine ⟨53831331952427071907661923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35887554634951381271774615 53831331952427071907661923)
        ·
          refine ⟨80746997928640607861492885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53831331952427071907661923 80746997928640607861492885)
          ·
            refine ⟨3785015527905028493507479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 80746997928640607861492885 3785015527905028493507479)
            ·
              refine ⟨5677523291857542740261219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3785015527905028493507479 5677523291857542740261219)
              ·
                refine ⟨8516284937786314110391829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5677523291857542740261219 8516284937786314110391829)
                ·
                  refine ⟨399200856458733473924617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8516284937786314110391829 399200856458733473924617)
                  ·
                    rfl

theorem cell21_1749242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 6].length) (baseStart_1749242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1749242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1749242 prefixEnd_1749242 := by exact prefixLift 1749242
  have htrace : WordTrace (prefixWord ++ tailWord_1749242) baseStart_1749242 baseEnd_1749242 := by
    simpa [prefixWord, tailWord_1749242, baseEnd_1749242] using wordTrace_append hprefix tailTrace_1749242
  have hstable : (prefixWord ++ tailWord_1749242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749242).length < 2 ^ (prefixWord ++ tailWord_1749242).sum := by decide
  have hdescent : baseEnd_1749242 < baseStart_1749242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749259 : List Nat := [1, 1, 1, 1, 5, 2, 5, 1, 4]
def baseStart_1749259 : Nat := 118140960795 + 1749259 * 2 ^ 59
def prefixEnd_1749259 : Nat := 4983230072969 + 3 ^ 40 * 1749259 * 2
def baseEnd_1749259 : Nat := 399204736090345222141249

theorem tailTrace_1749259 : CollatzResearch.WordTrace tailWord_1749259 prefixEnd_1749259 399204736090345222141249 := by
  unfold tailWord_1749259
  simp only [CollatzResearch.WordTrace]
  refine ⟨63800717169740867497634831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42533811446493911665089887 63800717169740867497634831)
  ·
    refine ⟨95701075754611301246452247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63800717169740867497634831 95701075754611301246452247)
    ·
      refine ⟨143551613631916951869678371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95701075754611301246452247 143551613631916951869678371)
      ·
        refine ⟨215327420447875427804517557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143551613631916951869678371 215327420447875427804517557)
        ·
          refine ⟨20186945666988321356673521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 215327420447875427804517557 20186945666988321356673521)
          ·
            refine ⟨15140209250241241017505141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20186945666988321356673521 15140209250241241017505141)
            ·
              refine ⟨1419394617210116345391107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15140209250241241017505141 1419394617210116345391107)
              ·
                refine ⟨2129091925815174518086661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1419394617210116345391107 2129091925815174518086661)
                ·
                  refine ⟨399204736090345222141249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2129091925815174518086661 399204736090345222141249)
                  ·
                    rfl

theorem cell21_1749259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 1, 4].length) (baseStart_1749259 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1749259 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1749259 prefixEnd_1749259 := by exact prefixLift 1749259
  have htrace : WordTrace (prefixWord ++ tailWord_1749259) baseStart_1749259 baseEnd_1749259 := by
    simpa [prefixWord, tailWord_1749259, baseEnd_1749259] using wordTrace_append hprefix tailTrace_1749259
  have hstable : (prefixWord ++ tailWord_1749259).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749259).length < 2 ^ (prefixWord ++ tailWord_1749259).sum := by decide
  have hdescent : baseEnd_1749259 < baseStart_1749259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749290 : List Nat := [3, 1, 4, 2, 2, 2, 7]
def baseStart_1749290 : Nat := 118140960795 + 1749290 * 2 ^ 59
def prefixEnd_1749290 : Nat := 4983230072969 + 3 ^ 40 * 1749290 * 2
def baseEnd_1749290 : Nat := 44356867856966228569391

theorem tailTrace_1749290 : CollatzResearch.WordTrace tailWord_1749290 prefixEnd_1749290 44356867856966228569391 := by
  unfold tailWord_1749290
  simp only [CollatzResearch.WordTrace]
  refine ⟨15950461958157139948003331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42534565221752373194675549 15950461958157139948003331)
  ·
    refine ⟨23925692937235709922004997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15950461958157139948003331 23925692937235709922004997)
    ·
      refine ⟨4486067425731695610375937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23925692937235709922004997 4486067425731695610375937)
      ·
        refine ⟨3364550569298771707781953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4486067425731695610375937 3364550569298771707781953)
        ·
          refine ⟨2523412926974078780836465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3364550569298771707781953 2523412926974078780836465)
          ·
            refine ⟨1892559695230559085627349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2523412926974078780836465 1892559695230559085627349)
            ·
              refine ⟨44356867856966228569391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1892559695230559085627349 44356867856966228569391)
              ·
                rfl

theorem cell21_1749290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 7].length) (baseStart_1749290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1749290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1749290 prefixEnd_1749290 := by exact prefixLift 1749290
  have htrace : WordTrace (prefixWord ++ tailWord_1749290) baseStart_1749290 baseEnd_1749290 := by
    simpa [prefixWord, tailWord_1749290, baseEnd_1749290] using wordTrace_append hprefix tailTrace_1749290
  have hstable : (prefixWord ++ tailWord_1749290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749290).length < 2 ^ (prefixWord ++ tailWord_1749290).sum := by decide
  have hdescent : baseEnd_1749290 < baseStart_1749290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749304 : List Nat := [2, 1, 2, 1, 3, 1, 2, 6, 3]
def baseStart_1749304 : Nat := 118140960795 + 1749304 * 2 ^ 59
def prefixEnd_1749304 : Nat := 4983230072969 + 3 ^ 40 * 1749304 * 2
def baseEnd_1749304 : Nat := 399215005703435143891157

theorem tailTrace_1749304 : CollatzResearch.WordTrace tailWord_1749304 prefixEnd_1749304 399215005703435143891157 := by
  unfold tailWord_1749304
  simp only [CollatzResearch.WordTrace]
  refine ⟨31901179227288920091511483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42534905636385226788681977 31901179227288920091511483)
  ·
    refine ⟨47851768840933380137267225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31901179227288920091511483 47851768840933380137267225)
    ·
      refine ⟨35888826630700035102950419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47851768840933380137267225 35888826630700035102950419)
      ·
        refine ⟨53833239946050052654425629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35888826630700035102950419 53833239946050052654425629)
        ·
          refine ⟨20187464979768769745409611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53833239946050052654425629 20187464979768769745409611)
          ·
            refine ⟨30281197469653154618114417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20187464979768769745409611 30281197469653154618114417)
            ·
              refine ⟨22710898102239865963585813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30281197469653154618114417 22710898102239865963585813)
              ·
                refine ⟨1064573348542493717043085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22710898102239865963585813 1064573348542493717043085)
                ·
                  refine ⟨399215005703435143891157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1064573348542493717043085 399215005703435143891157)
                  ·
                    rfl

theorem cell21_1749304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 6, 3].length) (baseStart_1749304 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1749304 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1749304 prefixEnd_1749304 := by exact prefixLift 1749304
  have htrace : WordTrace (prefixWord ++ tailWord_1749304) baseStart_1749304 baseEnd_1749304 := by
    simpa [prefixWord, tailWord_1749304, baseEnd_1749304] using wordTrace_append hprefix tailTrace_1749304
  have hstable : (prefixWord ++ tailWord_1749304).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749304).length < 2 ^ (prefixWord ++ tailWord_1749304).sum := by decide
  have hdescent : baseEnd_1749304 < baseStart_1749304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749408 : List Nat := [2, 1, 1, 4, 1, 4, 8]
def baseStart_1749408 : Nat := 118140960795 + 1749408 * 2 ^ 59
def prefixEnd_1749408 : Nat := 4983230072969 + 3 ^ 40 * 1749408 * 2
def baseEnd_1749408 : Nat := 44359859991150452684179

theorem tailTrace_1749408 : CollatzResearch.WordTrace tailWord_1749408 prefixEnd_1749408 44359859991150452684179 := by
  unfold tailWord_1749408
  simp only [CollatzResearch.WordTrace]
  refine ⟨31903075823100532972404439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42537434430800710629872585 31903075823100532972404439)
  ·
    refine ⟨47854613734650799458606659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31903075823100532972404439 47854613734650799458606659)
    ·
      refine ⟨71781920601976199187909989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47854613734650799458606659 71781920601976199187909989)
      ·
        refine ⟨13459110112870537347733123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71781920601976199187909989 13459110112870537347733123)
        ·
          refine ⟨20188665169305806021599685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13459110112870537347733123 20188665169305806021599685)
          ·
            refine ⟨3785374719244838629049941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20188665169305806021599685 3785374719244838629049941)
            ·
              refine ⟨44359859991150452684179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3785374719244838629049941 44359859991150452684179)
              ·
                rfl

theorem cell21_1749408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 8].length) (baseStart_1749408 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1749408 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1749408 prefixEnd_1749408 := by exact prefixLift 1749408
  have htrace : WordTrace (prefixWord ++ tailWord_1749408) baseStart_1749408 baseEnd_1749408 := by
    simpa [prefixWord, tailWord_1749408, baseEnd_1749408] using wordTrace_append hprefix tailTrace_1749408
  have hstable : (prefixWord ++ tailWord_1749408).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749408).length < 2 ^ (prefixWord ++ tailWord_1749408).sum := by decide
  have hdescent : baseEnd_1749408 < baseStart_1749408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749411 : List Nat := [1, 1, 1, 4, 1, 6, 1, 2, 4]
def baseStart_1749411 : Nat := 118140960795 + 1749411 * 2 ^ 59
def prefixEnd_1749411 : Nat := 4983230072969 + 3 ^ 40 * 1749411 * 2
def baseEnd_1749411 : Nat := 399239424561226735607605

theorem tailTrace_1749411 : CollatzResearch.WordTrace tailWord_1749411 prefixEnd_1749411 399239424561226735607605 := by
  unfold tailWord_1749411
  simp only [CollatzResearch.WordTrace]
  refine ⟨63806261065190197457168087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42537507376793464971445391 63806261065190197457168087)
  ·
    refine ⟨95709391597785296185752131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63806261065190197457168087 95709391597785296185752131)
    ·
      refine ⟨143564087396677944278628197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95709391597785296185752131 143564087396677944278628197)
      ·
        refine ⟨26918266386877114552242787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143564087396677944278628197 26918266386877114552242787)
        ·
          refine ⟨40377399580315671828364181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26918266386877114552242787 40377399580315671828364181)
          ·
            refine ⟨1892690605327297116954571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 40377399580315671828364181 1892690605327297116954571)
            ·
              refine ⟨2839035907990945675431857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1892690605327297116954571 2839035907990945675431857)
              ·
                refine ⟨2129276930993209256573893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2839035907990945675431857 2129276930993209256573893)
                ·
                  refine ⟨399239424561226735607605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2129276930993209256573893 399239424561226735607605)
                  ·
                    rfl

theorem cell21_1749411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 2, 4].length) (baseStart_1749411 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1749411 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1749411 prefixEnd_1749411 := by exact prefixLift 1749411
  have htrace : WordTrace (prefixWord ++ tailWord_1749411) baseStart_1749411 baseEnd_1749411 := by
    simpa [prefixWord, tailWord_1749411, baseEnd_1749411] using wordTrace_append hprefix tailTrace_1749411
  have hstable : (prefixWord ++ tailWord_1749411).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749411).length < 2 ^ (prefixWord ++ tailWord_1749411).sum := by decide
  have hdescent : baseEnd_1749411 < baseStart_1749411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749473 : List Nat := [1, 2, 3, 1, 2, 2, 5, 2, 3]
def baseStart_1749473 : Nat := 118140960795 + 1749473 * 2 ^ 59
def prefixEnd_1749473 : Nat := 4983230072969 + 3 ^ 40 * 1749473 * 2
def baseEnd_1749473 : Nat := 399253573805928405574145

theorem tailTrace_1749473 : CollatzResearch.WordTrace tailWord_1749473 prefixEnd_1749473 399253573805928405574145 := by
  unfold tailWord_1749473
  simp only [CollatzResearch.WordTrace]
  refine ⟨63808522390965582045925073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42539014927310388030616715 63808522390965582045925073)
  ·
    refine ⟨47856391793224186534443805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63808522390965582045925073 47856391793224186534443805)
    ·
      refine ⟨17946146922459069950416427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47856391793224186534443805 17946146922459069950416427)
      ·
        refine ⟨26919220383688604925624641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17946146922459069950416427 26919220383688604925624641)
        ·
          refine ⟨20189415287766453694218481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26919220383688604925624641 20189415287766453694218481)
          ·
            refine ⟨15142061465824840270663861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20189415287766453694218481 15142061465824840270663861)
            ·
              refine ⟨1419568262421078775374737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15142061465824840270663861 1419568262421078775374737)
              ·
                refine ⟨1064676196815809081531053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1419568262421078775374737 1064676196815809081531053)
                ·
                  refine ⟨399253573805928405574145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1064676196815809081531053 399253573805928405574145)
                  ·
                    rfl

theorem cell21_1749473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 2, 3].length) (baseStart_1749473 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1749473 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1749473 prefixEnd_1749473 := by exact prefixLift 1749473
  have htrace : WordTrace (prefixWord ++ tailWord_1749473) baseStart_1749473 baseEnd_1749473 := by
    simpa [prefixWord, tailWord_1749473, baseEnd_1749473] using wordTrace_append hprefix tailTrace_1749473
  have hstable : (prefixWord ++ tailWord_1749473).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749473).length < 2 ^ (prefixWord ++ tailWord_1749473).sum := by decide
  have hdescent : baseEnd_1749473 < baseStart_1749473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749484 : List Nat := [2, 2, 1, 1, 2, 1, 6, 6]
def baseStart_1749484 : Nat := 118140960795 + 1749484 * 2 ^ 59
def prefixEnd_1749484 : Nat := 4983230072969 + 3 ^ 40 * 1749484 * 2
def baseEnd_1749484 : Nat := 133085361385264943630263

theorem tailTrace_1749484 : CollatzResearch.WordTrace tailWord_1749484 prefixEnd_1749484 133085361385264943630263 := by
  unfold tailWord_1749484
  simp only [CollatzResearch.WordTrace]
  refine ⟨31904461796962865462287753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42539282395950487283050337 31904461796962865462287753)
  ·
    refine ⟨23928346347722149096715815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31904461796962865462287753 23928346347722149096715815)
    ·
      refine ⟨35892519521583223645073723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23928346347722149096715815 35892519521583223645073723)
      ·
        refine ⟨53838779282374835467610585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35892519521583223645073723 53838779282374835467610585)
        ·
          refine ⟨40379084461781126600707939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53838779282374835467610585 40379084461781126600707939)
          ·
            refine ⟨60568626692671689901061909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40379084461781126600707939 60568626692671689901061909)
            ·
              refine ⟨2839154376218985464112277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 60568626692671689901061909 2839154376218985464112277)
              ·
                refine ⟨133085361385264943630263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2839154376218985464112277 133085361385264943630263)
                ·
                  rfl

theorem cell21_1749484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 6].length) (baseStart_1749484 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1749484 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1749484 prefixEnd_1749484 := by exact prefixLift 1749484
  have htrace : WordTrace (prefixWord ++ tailWord_1749484) baseStart_1749484 baseEnd_1749484 := by
    simpa [prefixWord, tailWord_1749484, baseEnd_1749484] using wordTrace_append hprefix tailTrace_1749484
  have hstable : (prefixWord ++ tailWord_1749484).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749484).length < 2 ^ (prefixWord ++ tailWord_1749484).sum := by decide
  have hdescent : baseEnd_1749484 < baseStart_1749484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749591 : List Nat := [1, 1, 3, 2, 2, 2, 4, 1, 5]
def baseStart_1749591 : Nat := 118140960795 + 1749591 * 2 ^ 59
def prefixEnd_1749591 : Nat := 4983230072969 + 3 ^ 40 * 1749591 * 2
def baseEnd_1749591 : Nat := 399280503013586422607237

theorem tailTrace_1749591 : CollatzResearch.WordTrace tailWord_1749591 prefixEnd_1749591 399280503013586422607237 := by
  unfold tailWord_1749591
  simp only [CollatzResearch.WordTrace]
  refine ⟨63812826204538088198720627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42541884136358725465813751 63812826204538088198720627)
  ·
    refine ⟨95719239306807132298080941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63812826204538088198720627 95719239306807132298080941)
    ·
      refine ⟨35894714740052674611780353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95719239306807132298080941 35894714740052674611780353)
      ·
        refine ⟨26921036055039505958835265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35894714740052674611780353 26921036055039505958835265)
        ·
          refine ⟨20190777041279629469126449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26921036055039505958835265 20190777041279629469126449)
          ·
            refine ⟨15143082780959722101844837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20190777041279629469126449 15143082780959722101844837)
            ·
              refine ⟨2839328021429947894095907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15143082780959722101844837 2839328021429947894095907)
              ·
                refine ⟨4258992032144921841143861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2839328021429947894095907 4258992032144921841143861)
                ·
                  refine ⟨399280503013586422607237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4258992032144921841143861 399280503013586422607237)
                  ·
                    rfl

theorem cell21_1749591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 5].length) (baseStart_1749591 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1749591 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1749591 prefixEnd_1749591 := by exact prefixLift 1749591
  have htrace : WordTrace (prefixWord ++ tailWord_1749591) baseStart_1749591 baseEnd_1749591 := by
    simpa [prefixWord, tailWord_1749591, baseEnd_1749591] using wordTrace_append hprefix tailTrace_1749591
  have hstable : (prefixWord ++ tailWord_1749591).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749591).length < 2 ^ (prefixWord ++ tailWord_1749591).sum := by decide
  have hdescent : baseEnd_1749591 < baseStart_1749591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749625 : List Nat := [1, 2, 1, 3, 3, 4, 1, 3, 3]
def baseStart_1749625 : Nat := 118140960795 + 1749625 * 2 ^ 59
def prefixEnd_1749625 : Nat := 4983230072969 + 3 ^ 40 * 1749625 * 2
def baseEnd_1749625 : Nat := 399288262276809919040501

theorem tailTrace_1749625 : CollatzResearch.WordTrace tailWord_1749625 prefixEnd_1749625 399288262276809919040501 := by
  unfold tailWord_1749625
  simp only [CollatzResearch.WordTrace]
  refine ⟨63814066286414912005458329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42542710857609941336972219 63814066286414912005458329)
  ·
    refine ⟨47860549714811184004093747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63814066286414912005458329 47860549714811184004093747)
    ·
      refine ⟨71790824572216776006140621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47860549714811184004093747 71790824572216776006140621)
      ·
        refine ⟨26921559214581291002302733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71790824572216776006140621 26921559214581291002302733)
        ·
          refine ⟨10095584705467984125863525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26921559214581291002302733 10095584705467984125863525)
          ·
            refine ⟨1892922132275247023599411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10095584705467984125863525 1892922132275247023599411)
            ·
              refine ⟨2839383198412870535399117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1892922132275247023599411 2839383198412870535399117)
              ·
                refine ⟨1064768699404826450774669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2839383198412870535399117 1064768699404826450774669)
                ·
                  refine ⟨399288262276809919040501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1064768699404826450774669 399288262276809919040501)
                  ·
                    rfl

theorem cell21_1749625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 3, 3].length) (baseStart_1749625 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1749625 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1749625 prefixEnd_1749625 := by exact prefixLift 1749625
  have htrace : WordTrace (prefixWord ++ tailWord_1749625) baseStart_1749625 baseEnd_1749625 := by
    simpa [prefixWord, tailWord_1749625, baseEnd_1749625] using wordTrace_append hprefix tailTrace_1749625
  have hstable : (prefixWord ++ tailWord_1749625).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749625).length < 2 ^ (prefixWord ++ tailWord_1749625).sum := by decide
  have hdescent : baseEnd_1749625 < baseStart_1749625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749636 : List Nat := [2, 3, 2, 1, 3, 1, 9]
def baseStart_1749636 : Nat := 118140960795 + 1749636 * 2 ^ 59
def prefixEnd_1749636 : Nat := 4983230072969 + 3 ^ 40 * 1749636 * 2
def baseEnd_1749636 : Nat := 44365641402964038261905

theorem tailTrace_1749636 : CollatzResearch.WordTrace tailWord_1749636 prefixEnd_1749636 44365641402964038261905 := by
  unfold tailWord_1749636
  simp only [CollatzResearch.WordTrace]
  refine ⟨31907233744687530442054381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42542978326250040589405841 31907233744687530442054381)
  ·
    refine ⟨11965212654257823915770393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31907233744687530442054381 11965212654257823915770393)
    ·
      refine ⟨8973909490693367936827795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11965212654257823915770393 8973909490693367936827795)
      ·
        refine ⟨13460864236040051905241693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8973909490693367936827795 13460864236040051905241693)
        ·
          refine ⟨5047824088515019464465635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13460864236040051905241693 5047824088515019464465635)
          ·
            refine ⟨7571736132772529196698453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5047824088515019464465635 7571736132772529196698453)
            ·
              refine ⟨44365641402964038261905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7571736132772529196698453 44365641402964038261905)
              ·
                rfl

theorem cell21_1749636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 9].length) (baseStart_1749636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1749636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1749636 prefixEnd_1749636 := by exact prefixLift 1749636
  have htrace : WordTrace (prefixWord ++ tailWord_1749636) baseStart_1749636 baseEnd_1749636 := by
    simpa [prefixWord, tailWord_1749636, baseEnd_1749636] using wordTrace_append hprefix tailTrace_1749636
  have hstable : (prefixWord ++ tailWord_1749636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749636).length < 2 ^ (prefixWord ++ tailWord_1749636).sum := by decide
  have hdescent : baseEnd_1749636 < baseStart_1749636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749642 : List Nat := [3, 1, 2, 3, 3, 1, 3, 2, 3]
def baseStart_1749642 : Nat := 118140960795 + 1749642 * 2 ^ 59
def prefixEnd_1749642 : Nat := 4983230072969 + 3 ^ 40 * 1749642 * 2
def baseEnd_1749642 : Nat := 399292141908421667257133

theorem tailTrace_1749642 : CollatzResearch.WordTrace tailWord_1749642 prefixEnd_1749642 399292141908421667257133 := by
  unfold tailWord_1749642
  simp only [CollatzResearch.WordTrace]
  refine ⟨15953671581838330977206795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42543124218235549272551453 15953671581838330977206795)
  ·
    refine ⟨23930507372757496465810193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15953671581838330977206795 23930507372757496465810193)
    ·
      refine ⟨17947880529568122349357645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23930507372757496465810193 17947880529568122349357645)
      ·
        refine ⟨6730455198588045881009117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17947880529568122349357645 6730455198588045881009117)
        ·
          refine ⟨2523920699470517205378419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6730455198588045881009117 2523920699470517205378419)
          ·
            refine ⟨3785881049205775808067629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2523920699470517205378419 3785881049205775808067629)
            ·
              refine ⟨1419705393452165928025361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3785881049205775808067629 1419705393452165928025361)
              ·
                refine ⟨1064779045089124446019021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1419705393452165928025361 1064779045089124446019021)
                ·
                  refine ⟨399292141908421667257133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1064779045089124446019021 399292141908421667257133)
                  ·
                    rfl

theorem cell21_1749642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 2, 3].length) (baseStart_1749642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1749642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1749642 prefixEnd_1749642 := by exact prefixLift 1749642
  have htrace : WordTrace (prefixWord ++ tailWord_1749642) baseStart_1749642 baseEnd_1749642 := by
    simpa [prefixWord, tailWord_1749642, baseEnd_1749642] using wordTrace_append hprefix tailTrace_1749642
  have hstable : (prefixWord ++ tailWord_1749642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749642).length < 2 ^ (prefixWord ++ tailWord_1749642).sum := by decide
  have hdescent : baseEnd_1749642 < baseStart_1749642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749695 : List Nat := [1, 1, 2, 2, 2, 13]
def baseStart_1749695 : Nat := 118140960795 + 1749695 * 2 ^ 59
def prefixEnd_1749695 : Nat := 4983230072969 + 3 ^ 40 * 1749695 * 2
def baseEnd_1749695 : Nat := 14789045823352050106433

theorem tailTrace_1749695 : CollatzResearch.WordTrace tailWord_1749695 prefixEnd_1749695 14789045823352050106433 := by
  unfold tailWord_1749695
  simp only [CollatzResearch.WordTrace]
  refine ⟨63816619396161313960506539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42544412930774209307004359 63816619396161313960506539)
  ·
    refine ⟨95724929094241970940759809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63816619396161313960506539 95724929094241970940759809)
    ·
      refine ⟨71793696820681478205569857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95724929094241970940759809 71793696820681478205569857)
      ·
        refine ⟨53845272615511108654177393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71793696820681478205569857 53845272615511108654177393)
        ·
          refine ⟨40383954461633331490633045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53845272615511108654177393 40383954461633331490633045)
          ·
            refine ⟨14789045823352050106433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 40383954461633331490633045 14789045823352050106433)
            ·
              rfl

theorem cell21_1749695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 13].length) (baseStart_1749695 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1749695 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1749695 prefixEnd_1749695 := by exact prefixLift 1749695
  have htrace : WordTrace (prefixWord ++ tailWord_1749695) baseStart_1749695 baseEnd_1749695 := by
    simpa [prefixWord, tailWord_1749695, baseEnd_1749695] using wordTrace_append hprefix tailTrace_1749695
  have hstable : (prefixWord ++ tailWord_1749695).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749695).length < 2 ^ (prefixWord ++ tailWord_1749695).sum := by decide
  have hdescent : baseEnd_1749695 < baseStart_1749695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749729 : List Nat := [1, 2, 3, 1, 4, 2, 3, 5]
def baseStart_1749729 : Nat := 118140960795 + 1749729 * 2 ^ 59
def prefixEnd_1749729 : Nat := 4983230072969 + 3 ^ 40 * 1749729 * 2
def baseEnd_1749729 : Nat := 133103998831242949768985

theorem tailTrace_1749729 : CollatzResearch.WordTrace tailWord_1749729 prefixEnd_1749729 133103998831242949768985 := by
  unfold tailWord_1749729
  simp only [CollatzResearch.WordTrace]
  refine ⟨63817859478038137767244241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42545239652025425178162827 63817859478038137767244241)
  ·
    refine ⟨47863394608528603325433181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63817859478038137767244241 47863394608528603325433181)
    ·
      refine ⟨17948772978198226247037443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47863394608528603325433181 17948772978198226247037443)
      ·
        refine ⟨26923159467297339370556165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17948772978198226247037443 26923159467297339370556165)
        ·
          refine ⟨5048092400118251131979281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26923159467297339370556165 5048092400118251131979281)
          ·
            refine ⟨3786069300088688348984461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5048092400118251131979281 3786069300088688348984461)
            ·
              refine ⟨1419775987533258130869173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3786069300088688348984461 1419775987533258130869173)
              ·
                refine ⟨133103998831242949768985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1419775987533258130869173 133103998831242949768985)
                ·
                  rfl

theorem cell21_1749729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 5].length) (baseStart_1749729 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1749729 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1749729 prefixEnd_1749729 := by exact prefixLift 1749729
  have htrace : WordTrace (prefixWord ++ tailWord_1749729) baseStart_1749729 baseEnd_1749729 := by
    simpa [prefixWord, tailWord_1749729, baseEnd_1749729] using wordTrace_append hprefix tailTrace_1749729
  have hstable : (prefixWord ++ tailWord_1749729).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749729).length < 2 ^ (prefixWord ++ tailWord_1749729).sum := by decide
  have hdescent : baseEnd_1749729 < baseStart_1749729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749757 : List Nat := [1, 4, 1, 1, 1, 1, 5, 1, 6]
def baseStart_1749757 : Nat := 118140960795 + 1749757 * 2 ^ 59
def prefixEnd_1749757 : Nat := 4983230072969 + 3 ^ 40 * 1749757 * 2
def baseEnd_1749757 : Nat := 399318386475207022840231

theorem tailTrace_1749757 : CollatzResearch.WordTrace tailWord_1749757 prefixEnd_1749757 399318386475207022840231 := by
  unfold tailWord_1749757
  simp only [CollatzResearch.WordTrace]
  refine ⟨63818880721936698549263525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42545920481291132366175683 63818880721936698549263525)
  ·
    refine ⟨11966040135363130977986911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63818880721936698549263525 11966040135363130977986911)
    ·
      refine ⟨17949060203044696466980367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11966040135363130977986911 17949060203044696466980367)
      ·
        refine ⟨26923590304567044700470551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17949060203044696466980367 26923590304567044700470551)
        ·
          refine ⟨40385385456850567050705827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26923590304567044700470551 40385385456850567050705827)
          ·
            refine ⟨60578078185275850576058741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40385385456850567050705827 60578078185275850576058741)
            ·
              refine ⟨5679194829869610991505507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60578078185275850576058741 5679194829869610991505507)
              ·
                refine ⟨8518792244804416487258261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5679194829869610991505507 8518792244804416487258261)
                ·
                  refine ⟨399318386475207022840231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8518792244804416487258261 399318386475207022840231)
                  ·
                    rfl

theorem cell21_1749757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_1749757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1749757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1749757 prefixEnd_1749757 := by exact prefixLift 1749757
  have htrace : WordTrace (prefixWord ++ tailWord_1749757) baseStart_1749757 baseEnd_1749757 := by
    simpa [prefixWord, tailWord_1749757, baseEnd_1749757] using wordTrace_append hprefix tailTrace_1749757
  have hstable : (prefixWord ++ tailWord_1749757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749757).length < 2 ^ (prefixWord ++ tailWord_1749757).sum := by decide
  have hdescent : baseEnd_1749757 < baseStart_1749757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749771 : List Nat := [1, 1, 1, 1, 5, 1, 1, 10]
def baseStart_1749771 : Nat := 118140960795 + 1749771 * 2 ^ 59
def prefixEnd_1749771 : Nat := 4983230072969 + 3 ^ 40 * 1749771 * 2
def baseEnd_1749771 : Nat := 133107193821982036535623

theorem tailTrace_1749771 : CollatzResearch.WordTrace tailWord_1749771 prefixEnd_1749771 133107193821982036535623 := by
  unfold tailWord_1749771
  simp only [CollatzResearch.WordTrace]
  refine ⟨63819391343885978940273167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42546260895923985960182111 63819391343885978940273167)
  ·
    refine ⟨95729087015828968410409751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63819391343885978940273167 95729087015828968410409751)
    ·
      refine ⟨143593630523743452615614627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95729087015828968410409751 143593630523743452615614627)
      ·
        refine ⟨215390445785615178923421941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143593630523743452615614627 215390445785615178923421941)
        ·
          refine ⟨20192854292401423024070807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 215390445785615178923421941 20192854292401423024070807)
          ·
            refine ⟨30289281438602134536106211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20192854292401423024070807 30289281438602134536106211)
            ·
              refine ⟨45433922157903201804159317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30289281438602134536106211 45433922157903201804159317)
              ·
                refine ⟨133107193821982036535623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 45433922157903201804159317 133107193821982036535623)
                ·
                  rfl

theorem cell21_1749771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 10].length) (baseStart_1749771 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1749771 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1749771 prefixEnd_1749771 := by exact prefixLift 1749771
  have htrace : WordTrace (prefixWord ++ tailWord_1749771) baseStart_1749771 baseEnd_1749771 := by
    simpa [prefixWord, tailWord_1749771, baseEnd_1749771] using wordTrace_append hprefix tailTrace_1749771
  have hstable : (prefixWord ++ tailWord_1749771).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749771).length < 2 ^ (prefixWord ++ tailWord_1749771).sum := by decide
  have hdescent : baseEnd_1749771 < baseStart_1749771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749788 : List Nat := [2, 2, 3, 1, 1, 4, 1, 7]
def baseStart_1749788 : Nat := 118140960795 + 1749788 * 2 ^ 59
def prefixEnd_1749788 : Nat := 4983230072969 + 3 ^ 40 * 1749788 * 2
def baseEnd_1749788 : Nat := 133108487032519285941167

theorem tailTrace_1749788 : CollatzResearch.WordTrace tailWord_1749788 prefixEnd_1749788 133108487032519285941167 := by
  unfold tailWord_1749788
  simp only [CollatzResearch.WordTrace]
  refine ⟨31910005692412195421821009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42546674256549593895761345 31910005692412195421821009)
  ·
    refine ⟨23932504269309146566365757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31910005692412195421821009 23932504269309146566365757)
    ·
      refine ⟨8974689100990929962387159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23932504269309146566365757 8974689100990929962387159)
      ·
        refine ⟨13462033651486394943580739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8974689100990929962387159 13462033651486394943580739)
        ·
          refine ⟨20193050477229592415371109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13462033651486394943580739 20193050477229592415371109)
          ·
            refine ⟨3786196964480548577882083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20193050477229592415371109 3786196964480548577882083)
            ·
              refine ⟨5679295446720822866823125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3786196964480548577882083 5679295446720822866823125)
              ·
                refine ⟨133108487032519285941167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5679295446720822866823125 133108487032519285941167)
                ·
                  rfl

theorem cell21_1749788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 7].length) (baseStart_1749788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1749788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1749788 prefixEnd_1749788 := by exact prefixLift 1749788
  have htrace : WordTrace (prefixWord ++ tailWord_1749788) baseStart_1749788 baseEnd_1749788 := by
    simpa [prefixWord, tailWord_1749788, baseEnd_1749788] using wordTrace_append hprefix tailTrace_1749788
  have hstable : (prefixWord ++ tailWord_1749788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749788).length < 2 ^ (prefixWord ++ tailWord_1749788).sum := by decide
  have hdescent : baseEnd_1749788 < baseStart_1749788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749825 : List Nat := [1, 2, 5, 3, 1, 2, 2, 1, 4]
def baseStart_1749825 : Nat := 118140960795 + 1749825 * 2 ^ 59
def prefixEnd_1749825 : Nat := 4983230072969 + 3 ^ 40 * 1749825 * 2
def baseEnd_1749825 : Nat := 399333905001654015706759

theorem tailTrace_1749825 : CollatzResearch.WordTrace tailWord_1749825 prefixEnd_1749825 399333905001654015706759 := by
  unfold tailWord_1749825
  simp only [CollatzResearch.WordTrace]
  refine ⟨63821360885690346162738929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42547573923793564108492619 63821360885690346162738929)
  ·
    refine ⟨47866020664267759622054197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63821360885690346162738929 47866020664267759622054197)
    ·
      refine ⟨4487439437275102464567581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47866020664267759622054197 4487439437275102464567581)
      ·
        refine ⟨1682789788978163424212843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4487439437275102464567581 1682789788978163424212843)
        ·
          refine ⟨2524184683467245136319265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1682789788978163424212843 2524184683467245136319265)
          ·
            refine ⟨1893138512600433852239449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2524184683467245136319265 1893138512600433852239449)
            ·
              refine ⟨1419853884450325389179587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1893138512600433852239449 1419853884450325389179587)
              ·
                refine ⟨2129780826675488083769381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1419853884450325389179587 2129780826675488083769381)
                ·
                  refine ⟨399333905001654015706759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2129780826675488083769381 399333905001654015706759)
                  ·
                    rfl

theorem cell21_1749825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 1, 4].length) (baseStart_1749825 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1749825 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1749825 prefixEnd_1749825 := by exact prefixLift 1749825
  have htrace : WordTrace (prefixWord ++ tailWord_1749825) baseStart_1749825 baseEnd_1749825 := by
    simpa [prefixWord, tailWord_1749825, baseEnd_1749825] using wordTrace_append hprefix tailTrace_1749825
  have hstable : (prefixWord ++ tailWord_1749825).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749825).length < 2 ^ (prefixWord ++ tailWord_1749825).sum := by decide
  have hdescent : baseEnd_1749825 < baseStart_1749825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749895 : List Nat := [1, 1, 4, 2, 3, 2, 1, 2, 5]
def baseStart_1749895 : Nat := 118140960795 + 1749895 * 2 ^ 59
def prefixEnd_1749895 : Nat := 4983230072969 + 3 ^ 40 * 1749895 * 2
def baseEnd_1749895 : Nat := 399349879955349449539949

theorem tailTrace_1749895 : CollatzResearch.WordTrace tailWord_1749895 prefixEnd_1749895 399349879955349449539949 := by
  unfold tailWord_1749895
  simp only [CollatzResearch.WordTrace]
  refine ⟨63823913995436748117787139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42549275996957832078524759 63823913995436748117787139)
  ·
    refine ⟨95735870993155122176680709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63823913995436748117787139 95735870993155122176680709)
    ·
      refine ⟨17950475811216585408127633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95735870993155122176680709 17950475811216585408127633)
      ·
        refine ⟨13462856858412439056095725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17950475811216585408127633 13462856858412439056095725)
        ·
          refine ⟨5048571321904664646035897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13462856858412439056095725 5048571321904664646035897)
          ·
            refine ⟨3786428491428498484526923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5048571321904664646035897 3786428491428498484526923)
            ·
              refine ⟨5679642737142747726790385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3786428491428498484526923 5679642737142747726790385)
              ·
                refine ⟨4259732052857060795092789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5679642737142747726790385 4259732052857060795092789)
                ·
                  refine ⟨399349879955349449539949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4259732052857060795092789 399349879955349449539949)
                  ·
                    rfl

theorem cell21_1749895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 5].length) (baseStart_1749895 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1749895 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1749895 prefixEnd_1749895 := by exact prefixLift 1749895
  have htrace : WordTrace (prefixWord ++ tailWord_1749895) baseStart_1749895 baseEnd_1749895 := by
    simpa [prefixWord, tailWord_1749895, baseEnd_1749895] using wordTrace_append hprefix tailTrace_1749895
  have hstable : (prefixWord ++ tailWord_1749895).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749895).length < 2 ^ (prefixWord ++ tailWord_1749895).sum := by decide
  have hdescent : baseEnd_1749895 < baseStart_1749895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749985 : List Nat := [1, 2, 3, 1, 2, 1, 1, 6, 4]
def baseStart_1749985 : Nat := 118140960795 + 1749985 * 2 ^ 59
def prefixEnd_1749985 : Nat := 4983230072969 + 3 ^ 40 * 1749985 * 2
def baseEnd_1749985 : Nat := 399370419181529293039765

theorem tailTrace_1749985 : CollatzResearch.WordTrace tailWord_1749985 prefixEnd_1749985 399370419181529293039765 := by
  unfold tailWord_1749985
  simp only [CollatzResearch.WordTrace]
  refine ⟨63827196565110693488563409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42551464376740462325708939 63827196565110693488563409)
  ·
    refine ⟨47870397423833020116422557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63827196565110693488563409 47870397423833020116422557)
    ·
      refine ⟨17951399033937382543658459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47870397423833020116422557 17951399033937382543658459)
      ·
        refine ⟨26927098550906073815487689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17951399033937382543658459 26927098550906073815487689)
        ·
          refine ⟨20195323913179555361615767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26927098550906073815487689 20195323913179555361615767)
          ·
            refine ⟨30292985869769333042423651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20195323913179555361615767 30292985869769333042423651)
            ·
              refine ⟨45439478804653999563635477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30292985869769333042423651 45439478804653999563635477)
              ·
                refine ⟨2129975568968156229545413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45439478804653999563635477 2129975568968156229545413)
                ·
                  refine ⟨399370419181529293039765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2129975568968156229545413 399370419181529293039765)
                  ·
                    rfl

theorem cell21_1749985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 6, 4].length) (baseStart_1749985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1749985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1749985 prefixEnd_1749985 := by exact prefixLift 1749985
  have htrace : WordTrace (prefixWord ++ tailWord_1749985) baseStart_1749985 baseEnd_1749985 := by
    simpa [prefixWord, tailWord_1749985, baseEnd_1749985] using wordTrace_append hprefix tailTrace_1749985
  have hstable : (prefixWord ++ tailWord_1749985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749985).length < 2 ^ (prefixWord ++ tailWord_1749985).sum := by decide
  have hdescent : baseEnd_1749985 < baseStart_1749985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1749999 : List Nat := [1, 1, 2, 1, 4, 3, 1, 8]
def baseStart_1749999 : Nat := 118140960795 + 1749999 * 2 ^ 59
def prefixEnd_1749999 : Nat := 4983230072969 + 3 ^ 40 * 1749999 * 2
def baseEnd_1749999 : Nat := 133124538057422793268801

theorem tailTrace_1749999 : CollatzResearch.WordTrace tailWord_1749999 prefixEnd_1749999 133124538057422793268801 := by
  unfold tailWord_1749999
  simp only [CollatzResearch.WordTrace]
  refine ⟨63827707187059973879573051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42551804791373315919715367 63827707187059973879573051)
  ·
    refine ⟨95741560780589960819359577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63827707187059973879573051 95741560780589960819359577)
    ·
      refine ⟨71806170585442470614519683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95741560780589960819359577 71806170585442470614519683)
      ·
        refine ⟨107709255878163705921779525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71806170585442470614519683 107709255878163705921779525)
        ·
          refine ⟨20195485477155694860333661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107709255878163705921779525 20195485477155694860333661)
          ·
            refine ⟨7573307053933385572625123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20195485477155694860333661 7573307053933385572625123)
            ·
              refine ⟨11359960580900078358937685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7573307053933385572625123 11359960580900078358937685)
              ·
                refine ⟨133124538057422793268801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11359960580900078358937685 133124538057422793268801)
                ·
                  rfl

theorem cell21_1749999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 8].length) (baseStart_1749999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1749999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1749999 prefixEnd_1749999 := by exact prefixLift 1749999
  have htrace : WordTrace (prefixWord ++ tailWord_1749999) baseStart_1749999 baseEnd_1749999 := by
    simpa [prefixWord, tailWord_1749999, baseEnd_1749999] using wordTrace_append hprefix tailTrace_1749999
  have hstable : (prefixWord ++ tailWord_1749999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1749999).length < 2 ^ (prefixWord ++ tailWord_1749999).sum := by decide
  have hdescent : baseEnd_1749999 < baseStart_1749999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1749999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750081 : List Nat := [1, 2, 5, 1, 3, 1, 2, 3, 3]
def baseStart_1750081 : Nat := 118140960795 + 1750081 * 2 ^ 59
def prefixEnd_1750081 : Nat := 4983230072969 + 3 ^ 40 * 1750081 * 2
def baseEnd_1750081 : Nat := 399392327689454459439569

theorem tailTrace_1750081 : CollatzResearch.WordTrace tailWord_1750081 prefixEnd_1750081 399392327689454459439569 := by
  unfold tailWord_1750081
  simp only [CollatzResearch.WordTrace]
  refine ⟨63830697972762901884058097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42553798648508601256038731 63830697972762901884058097)
  ·
    refine ⟨47873023479572176413043573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63830697972762901884058097 47873023479572176413043573)
    ·
      refine ⟨4488095951209891538722835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47873023479572176413043573 4488095951209891538722835)
      ·
        refine ⟨6732143926814837308084253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4488095951209891538722835 6732143926814837308084253)
        ·
          refine ⟨2524553972555563990531595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6732143926814837308084253 2524553972555563990531595)
          ·
            refine ⟨3786830958833345985797393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2524553972555563990531595 3786830958833345985797393)
            ·
              refine ⟨2840123219125009489348045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3786830958833345985797393 2840123219125009489348045)
              ·
                refine ⟨1065046207171878558505517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2840123219125009489348045 1065046207171878558505517)
                ·
                  refine ⟨399392327689454459439569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1065046207171878558505517 399392327689454459439569)
                  ·
                    rfl

theorem cell21_1750081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 3, 3].length) (baseStart_1750081 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1750081 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1750081 prefixEnd_1750081 := by exact prefixLift 1750081
  have htrace : WordTrace (prefixWord ++ tailWord_1750081) baseStart_1750081 baseEnd_1750081 := by
    simpa [prefixWord, tailWord_1750081, baseEnd_1750081] using wordTrace_append hprefix tailTrace_1750081
  have hstable : (prefixWord ++ tailWord_1750081).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750081).length < 2 ^ (prefixWord ++ tailWord_1750081).sum := by decide
  have hdescent : baseEnd_1750081 < baseStart_1750081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750168 : List Nat := [2, 1, 2, 4, 2, 2, 2, 6]
def baseStart_1750168 : Nat := 118140960795 + 1750168 * 2 ^ 59
def prefixEnd_1750168 : Nat := 4983230072969 + 3 ^ 40 * 1750168 * 2
def baseEnd_1750168 : Nat := 133137394091587213829797

theorem tailTrace_1750168 : CollatzResearch.WordTrace tailWord_1750168 prefixEnd_1750168 133137394091587213829797 := by
  unfold tailWord_1750168
  simp only [CollatzResearch.WordTrace]
  refine ⟨31916935561723857871237579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42555914082298477161650105 31916935561723857871237579)
  ·
    refine ⟨47875403342585786806856369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31916935561723857871237579 47875403342585786806856369)
    ·
      refine ⟨35906552506939340105142277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47875403342585786806856369 35906552506939340105142277)
      ·
        refine ⟨6732478595051126269714177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35906552506939340105142277 6732478595051126269714177)
        ·
          refine ⟨5049358946288344702285633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6732478595051126269714177 5049358946288344702285633)
          ·
            refine ⟨3787019209716258526714225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5049358946288344702285633 3787019209716258526714225)
            ·
              refine ⟨2840264407287193895035669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3787019209716258526714225 2840264407287193895035669)
              ·
                refine ⟨133137394091587213829797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2840264407287193895035669 133137394091587213829797)
                ·
                  rfl

theorem cell21_1750168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 6].length) (baseStart_1750168 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1750168 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1750168 prefixEnd_1750168 := by exact prefixLift 1750168
  have htrace : WordTrace (prefixWord ++ tailWord_1750168) baseStart_1750168 baseEnd_1750168 := by
    simpa [prefixWord, tailWord_1750168, baseEnd_1750168] using wordTrace_append hprefix tailTrace_1750168
  have hstable : (prefixWord ++ tailWord_1750168).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750168).length < 2 ^ (prefixWord ++ tailWord_1750168).sum := by decide
  have hdescent : baseEnd_1750168 < baseStart_1750168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750199 : List Nat := [1, 1, 3, 1, 4, 1, 2, 5, 3]
def baseStart_1750199 : Nat := 118140960795 + 1750199 * 2 ^ 59
def prefixEnd_1750199 : Nat := 4983230072969 + 3 ^ 40 * 1750199 * 2
def baseEnd_1750199 : Nat := 399419256897112476472661

theorem tailTrace_1750199 : CollatzResearch.WordTrace tailWord_1750199 prefixEnd_1750199 399419256897112476472661 := by
  unfold tailWord_1750199
  simp only [CollatzResearch.WordTrace]
  refine ⟨63835001786335408036853651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42556667857556938691235767 63835001786335408036853651)
  ·
    refine ⟨95752502679503112055280477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63835001786335408036853651 95752502679503112055280477)
    ·
      refine ⟨35907188504813667020730179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95752502679503112055280477 35907188504813667020730179)
      ·
        refine ⟨53860782757220500531095269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35907188504813667020730179 53860782757220500531095269)
        ·
          refine ⟨10098896766978843849580363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53860782757220500531095269 10098896766978843849580363)
          ·
            refine ⟨15148345150468265774370545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10098896766978843849580363 15148345150468265774370545)
            ·
              refine ⟨11361258862851199330777909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15148345150468265774370545 11361258862851199330777909)
              ·
                refine ⟨1065118018392299937260429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11361258862851199330777909 1065118018392299937260429)
                ·
                  refine ⟨399419256897112476472661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1065118018392299937260429 399419256897112476472661)
                  ·
                    rfl

theorem cell21_1750199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 5, 3].length) (baseStart_1750199 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1750199 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1750199 prefixEnd_1750199 := by exact prefixLift 1750199
  have htrace : WordTrace (prefixWord ++ tailWord_1750199) baseStart_1750199 baseEnd_1750199 := by
    simpa [prefixWord, tailWord_1750199, baseEnd_1750199] using wordTrace_append hprefix tailTrace_1750199
  have hstable : (prefixWord ++ tailWord_1750199).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750199).length < 2 ^ (prefixWord ++ tailWord_1750199).sum := by decide
  have hdescent : baseEnd_1750199 < baseStart_1750199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750216 : List Nat := [2, 1, 3, 1, 2, 1, 6, 2, 3]
def baseStart_1750216 : Nat := 118140960795 + 1750216 * 2 ^ 59
def prefixEnd_1750216 : Nat := 4983230072969 + 3 ^ 40 * 1750216 * 2
def baseEnd_1750216 : Nat := 399423136528724224689293

theorem tailTrace_1750216 : CollatzResearch.WordTrace tailWord_1750216 prefixEnd_1750216 399423136528724224689293 := by
  unfold tailWord_1750216
  simp only [CollatzResearch.WordTrace]
  refine ⟨31917810913636909970111251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42557081218182546626815001 31917810913636909970111251)
  ·
    refine ⟨47876716370455364955166877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31917810913636909970111251 47876716370455364955166877)
    ·
      refine ⟨17953768638920761858187579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47876716370455364955166877 17953768638920761858187579)
      ·
        refine ⟨26930652958381142787281369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17953768638920761858187579 26930652958381142787281369)
        ·
          refine ⟨20197989718785857090461027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26930652958381142787281369 20197989718785857090461027)
          ·
            refine ⟨30296984578178785635691541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20197989718785857090461027 30296984578178785635691541)
            ·
              refine ⟨1420171152102130576673041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30296984578178785635691541 1420171152102130576673041)
              ·
                refine ⟨1065128364076597932504781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1420171152102130576673041 1065128364076597932504781)
                ·
                  refine ⟨399423136528724224689293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1065128364076597932504781 399423136528724224689293)
                  ·
                    rfl

theorem cell21_1750216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 2, 3].length) (baseStart_1750216 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1750216 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1750216 prefixEnd_1750216 := by exact prefixLift 1750216
  have htrace : WordTrace (prefixWord ++ tailWord_1750216) baseStart_1750216 baseEnd_1750216 := by
    simpa [prefixWord, tailWord_1750216, baseEnd_1750216] using wordTrace_append hprefix tailTrace_1750216
  have hstable : (prefixWord ++ tailWord_1750216).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750216).length < 2 ^ (prefixWord ++ tailWord_1750216).sum := by decide
  have hdescent : baseEnd_1750216 < baseStart_1750216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750275 : List Nat := [1, 1, 1, 3, 2, 4, 2, 4, 3]
def baseStart_1750275 : Nat := 118140960795 + 1750275 * 2 ^ 59
def prefixEnd_1750275 : Nat := 4983230072969 + 3 ^ 40 * 1750275 * 2
def baseEnd_1750275 : Nat := 399436601132553233205839

theorem tailTrace_1750275 : CollatzResearch.WordTrace tailWord_1750275 prefixEnd_1750275 399436601132553233205839 := by
  unfold tailWord_1750275
  simp only [CollatzResearch.WordTrace]
  refine ⟨63837773734060073016620279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42558515822706715344413519 63837773734060073016620279)
  ·
    refine ⟨95756660601090109524930419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63837773734060073016620279 95756660601090109524930419)
    ·
      refine ⟨143634990901635164287395629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95756660601090109524930419 143634990901635164287395629)
      ·
        refine ⟨53863121588113186607773361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143634990901635164287395629 53863121588113186607773361)
        ·
          refine ⟨40397341191084889955830021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53863121588113186607773361 40397341191084889955830021)
          ·
            refine ⟨7574501473328416866718129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40397341191084889955830021 7574501473328416866718129)
            ·
              refine ⟨5680876104996312650038597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7574501473328416866718129 5680876104996312650038597)
              ·
                refine ⟨1065164269686808621882237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5680876104996312650038597 1065164269686808621882237)
                ·
                  refine ⟨399436601132553233205839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1065164269686808621882237 399436601132553233205839)
                  ·
                    rfl

theorem cell21_1750275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 4, 3].length) (baseStart_1750275 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1750275 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1750275 prefixEnd_1750275 := by exact prefixLift 1750275
  have htrace : WordTrace (prefixWord ++ tailWord_1750275) baseStart_1750275 baseEnd_1750275 := by
    simpa [prefixWord, tailWord_1750275, baseEnd_1750275] using wordTrace_append hprefix tailTrace_1750275
  have hstable : (prefixWord ++ tailWord_1750275).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750275).length < 2 ^ (prefixWord ++ tailWord_1750275).sum := by decide
  have hdescent : baseEnd_1750275 < baseStart_1750275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750326 : List Nat := [5, 1, 2, 3, 2, 1, 1, 1, 5]
def baseStart_1750326 : Nat := 118140960795 + 1750326 * 2 ^ 59
def prefixEnd_1750326 : Nat := 4983230072969 + 3 ^ 40 * 1750326 * 2
def baseEnd_1750326 : Nat := 399448240027388477855735

theorem tailTrace_1750326 : CollatzResearch.WordTrace tailWord_1750326 prefixEnd_1750326 399448240027388477855735 := by
  unfold tailWord_1750326
  simp only [CollatzResearch.WordTrace]
  refine ⟨3989977116054706795420427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42559755904583539151151221 3989977116054706795420427)
  ·
    refine ⟨5984965674082060193130641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3989977116054706795420427 5984965674082060193130641)
    ·
      refine ⟨4488724255561545144847981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5984965674082060193130641 4488724255561545144847981)
      ·
        refine ⟨1683271595835579429317993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4488724255561545144847981 1683271595835579429317993)
        ·
          refine ⟨1262453696876684571988495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1683271595835579429317993 1262453696876684571988495)
          ·
            refine ⟨1893680545315026857982743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1262453696876684571988495 1893680545315026857982743)
            ·
              refine ⟨2840520817972540286974115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1893680545315026857982743 2840520817972540286974115)
              ·
                refine ⟨4260781226958810430461173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2840520817972540286974115 4260781226958810430461173)
                ·
                  refine ⟨399448240027388477855735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4260781226958810430461173 399448240027388477855735)
                  ·
                    rfl

theorem cell21_1750326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_1750326 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1750326 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1750326 prefixEnd_1750326 := by exact prefixLift 1750326
  have htrace : WordTrace (prefixWord ++ tailWord_1750326) baseStart_1750326 baseEnd_1750326 := by
    simpa [prefixWord, tailWord_1750326, baseEnd_1750326] using wordTrace_append hprefix tailTrace_1750326
  have hstable : (prefixWord ++ tailWord_1750326).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750326).length < 2 ^ (prefixWord ++ tailWord_1750326).sum := by decide
  have hdescent : baseEnd_1750326 < baseStart_1750326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750340 : List Nat := [2, 3, 4, 1, 1, 3, 2, 1, 4]
def baseStart_1750340 : Nat := 118140960795 + 1750340 * 2 ^ 59
def prefixEnd_1750340 : Nat := 4983230072969 + 3 ^ 40 * 1750340 * 2
def baseEnd_1750340 : Nat := 399451435018127564622373

theorem tailTrace_1750340 : CollatzResearch.WordTrace tailWord_1750340 prefixEnd_1750340 399451435018127564622373 := by
  unfold tailWord_1750340
  simp only [CollatzResearch.WordTrace]
  refine ⟨31920072239412294558868237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42560096319216392745157649 31920072239412294558868237)
  ·
    refine ⟨11970027089779610459575589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31920072239412294558868237 11970027089779610459575589)
    ·
      refine ⟨2244380079333676961170423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11970027089779610459575589 2244380079333676961170423)
      ·
        refine ⟨3366570119000515441755635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2244380079333676961170423 3366570119000515441755635)
        ·
          refine ⟨5049855178500773162633453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3366570119000515441755635 5049855178500773162633453)
          ·
            refine ⟨1893695691937789935987545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5049855178500773162633453 1893695691937789935987545)
            ·
              refine ⟨1420271768953342451990659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1893695691937789935987545 1420271768953342451990659)
              ·
                refine ⟨2130407653430013677985989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1420271768953342451990659 2130407653430013677985989)
                ·
                  refine ⟨399451435018127564622373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2130407653430013677985989 399451435018127564622373)
                  ·
                    rfl

theorem cell21_1750340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_1750340 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1750340 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1750340 prefixEnd_1750340 := by exact prefixLift 1750340
  have htrace : WordTrace (prefixWord ++ tailWord_1750340) baseStart_1750340 baseEnd_1750340 := by
    simpa [prefixWord, tailWord_1750340, baseEnd_1750340] using wordTrace_append hprefix tailTrace_1750340
  have hstable : (prefixWord ++ tailWord_1750340).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750340).length < 2 ^ (prefixWord ++ tailWord_1750340).sum := by decide
  have hdescent : baseEnd_1750340 < baseStart_1750340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750503 : List Nat := [1, 1, 5, 2, 1, 4, 1, 1, 5]
def baseStart_1750503 : Nat := 118140960795 + 1750503 * 2 ^ 59
def prefixEnd_1750503 : Nat := 4983230072969 + 3 ^ 40 * 1750503 * 2
def baseEnd_1750503 : Nat := 399488633838875503405373

theorem tailTrace_1750503 : CollatzResearch.WordTrace tailWord_1750503 prefixEnd_1750503 399488633838875503405373 := by
  unfold tailWord_1750503
  simp only [CollatzResearch.WordTrace]
  refine ⟨63846089577234067955920163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42564059718156045303946775 63846089577234067955920163)
  ·
    refine ⟨95769134365851101933880245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63846089577234067955920163 95769134365851101933880245)
    ·
      refine ⟨8978356346798540806301273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95769134365851101933880245 8978356346798540806301273)
      ·
        refine ⟨6733767260098905604725955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8978356346798540806301273 6733767260098905604725955)
        ·
          refine ⟨10100650890148358407088933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6733767260098905604725955 10100650890148358407088933)
          ·
            refine ⟨1893872041902817201329175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10100650890148358407088933 1893872041902817201329175)
            ·
              refine ⟨2840808062854225801993763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1893872041902817201329175 2840808062854225801993763)
              ·
                refine ⟨4261212094281338702990645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2840808062854225801993763 4261212094281338702990645)
                ·
                  refine ⟨399488633838875503405373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4261212094281338702990645 399488633838875503405373)
                  ·
                    rfl

theorem cell21_1750503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 5].length) (baseStart_1750503 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1750503 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1750503 prefixEnd_1750503 := by exact prefixLift 1750503
  have htrace : WordTrace (prefixWord ++ tailWord_1750503) baseStart_1750503 baseEnd_1750503 := by
    simpa [prefixWord, tailWord_1750503, baseEnd_1750503] using wordTrace_append hprefix tailTrace_1750503
  have hstable : (prefixWord ++ tailWord_1750503).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750503).length < 2 ^ (prefixWord ++ tailWord_1750503).sum := by decide
  have hdescent : baseEnd_1750503 < baseStart_1750503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750548 : List Nat := [2, 4, 3, 1, 2, 9]
def baseStart_1750548 : Nat := 118140960795 + 1750548 * 2 ^ 59
def prefixEnd_1750548 : Nat := 4983230072969 + 3 ^ 40 * 1750548 * 2
def baseEnd_1750548 : Nat := 14796255683406126857603

theorem tailTrace_1750548 : CollatzResearch.WordTrace tailWord_1750548 prefixEnd_1750548 14796255683406126857603 := by
  unfold tailWord_1750548
  simp only [CollatzResearch.WordTrace]
  refine ⟨31923865431035520320654149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42565153908047360427538865 31923865431035520320654149)
  ·
    refine ⟨5985724768319160060122653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31923865431035520320654149 5985724768319160060122653)
    ·
      refine ⟨2244646788119685022545995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5985724768319160060122653 2244646788119685022545995)
      ·
        refine ⟨3366970182179527533818993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2244646788119685022545995 3366970182179527533818993)
        ·
          refine ⟨2525227636634645650364245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3366970182179527533818993 2525227636634645650364245)
          ·
            refine ⟨14796255683406126857603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2525227636634645650364245 14796255683406126857603)
            ·
              rfl

theorem cell21_1750548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 9].length) (baseStart_1750548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1750548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1750548 prefixEnd_1750548 := by exact prefixLift 1750548
  have htrace : WordTrace (prefixWord ++ tailWord_1750548) baseStart_1750548 baseEnd_1750548 := by
    simpa [prefixWord, tailWord_1750548, baseEnd_1750548] using wordTrace_append hprefix tailTrace_1750548
  have hstable : (prefixWord ++ tailWord_1750548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750548).length < 2 ^ (prefixWord ++ tailWord_1750548).sum := by decide
  have hdescent : baseEnd_1750548 < baseStart_1750548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750610 : List Nat := [3, 2, 2, 1, 2, 4, 1, 2, 4]
def baseStart_1750610 : Nat := 118140960795 + 1750610 * 2 ^ 59
def prefixEnd_1750610 : Nat := 4983230072969 + 3 ^ 40 * 1750610 * 2
def baseEnd_1750610 : Nat := 399513052696667095121821

theorem tailTrace_1750610 : CollatzResearch.WordTrace tailWord_1750610 prefixEnd_1750610 399513052696667095121821 := by
  unfold tailWord_1750610
  simp only [CollatzResearch.WordTrace]
  refine ⟨15962498046961606307516321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42566661458564283486710189 15962498046961606307516321)
  ·
    refine ⟨11971873535221204730637241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15962498046961606307516321 11971873535221204730637241)
    ·
      refine ⟨8978905151415903547977931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11971873535221204730637241 8978905151415903547977931)
      ·
        refine ⟨13468357727123855321966897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8978905151415903547977931 13468357727123855321966897)
        ·
          refine ⟨10101268295342891491475173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13468357727123855321966897 10101268295342891491475173)
          ·
            refine ⟨1893987805376792154651595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10101268295342891491475173 1893987805376792154651595)
            ·
              refine ⟨2840981708065188231977393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1893987805376792154651595 2840981708065188231977393)
              ·
                refine ⟨2130736281048891173983045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2840981708065188231977393 2130736281048891173983045)
                ·
                  refine ⟨399513052696667095121821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2130736281048891173983045 399513052696667095121821)
                  ·
                    rfl

theorem cell21_1750610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_1750610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1750610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1750610 prefixEnd_1750610 := by exact prefixLift 1750610
  have htrace : WordTrace (prefixWord ++ tailWord_1750610) baseStart_1750610 baseEnd_1750610 := by
    simpa [prefixWord, tailWord_1750610, baseEnd_1750610] using wordTrace_append hprefix tailTrace_1750610
  have hstable : (prefixWord ++ tailWord_1750610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750610).length < 2 ^ (prefixWord ++ tailWord_1750610).sum := by decide
  have hdescent : baseEnd_1750610 < baseStart_1750610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750686 : List Nat := [4, 3, 1, 1, 1, 3, 1, 3, 4]
def baseStart_1750686 : Nat := 118140960795 + 1750686 * 2 ^ 59
def prefixEnd_1750686 : Nat := 4983230072969 + 3 ^ 40 * 1750686 * 2
def baseEnd_1750686 : Nat := 399530396932107851854999

theorem tailTrace_1750686 : CollatzResearch.WordTrace tailWord_1750686 prefixEnd_1750686 399530396932107851854999 := by
  unfold tailWord_1750686
  simp only [CollatzResearch.WordTrace]
  refine ⟨7981595516946386276228989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42568509423714060139887941 7981595516946386276228989)
  ·
    refine ⟨2993098318854894853585871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7981595516946386276228989 2993098318854894853585871)
    ·
      refine ⟨4489647478282342280378807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2993098318854894853585871 4489647478282342280378807)
      ·
        refine ⟨6734471217423513420568211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4489647478282342280378807 6734471217423513420568211)
        ·
          refine ⟨10101706826135270130852317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6734471217423513420568211 10101706826135270130852317)
          ·
            refine ⟨3788140059800726299069619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10101706826135270130852317 3788140059800726299069619)
            ·
              refine ⟨5682210089701089448604429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3788140059800726299069619 5682210089701089448604429)
              ·
                refine ⟨2130828783637908543226661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5682210089701089448604429 2130828783637908543226661)
                ·
                  refine ⟨399530396932107851854999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2130828783637908543226661 399530396932107851854999)
                  ·
                    rfl

theorem cell21_1750686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_1750686 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1750686 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1750686 prefixEnd_1750686 := by exact prefixLift 1750686
  have htrace : WordTrace (prefixWord ++ tailWord_1750686) baseStart_1750686 baseEnd_1750686 := by
    simpa [prefixWord, tailWord_1750686, baseEnd_1750686] using wordTrace_append hprefix tailTrace_1750686
  have hstable : (prefixWord ++ tailWord_1750686).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750686).length < 2 ^ (prefixWord ++ tailWord_1750686).sum := by decide
  have hdescent : baseEnd_1750686 < baseStart_1750686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750824 : List Nat := [2, 1, 5, 1, 1, 4, 1, 3, 3]
def baseStart_1750824 : Nat := 118140960795 + 1750824 * 2 ^ 59
def prefixEnd_1750824 : Nat := 4983230072969 + 3 ^ 40 * 1750824 * 2
def baseEnd_1750824 : Nat := 399561890412250278554717

theorem tailTrace_1750824 : CollatzResearch.WordTrace tailWord_1750824 prefixEnd_1750824 399561890412250278554717 := by
  unfold tailWord_1750824
  simp only [CollatzResearch.WordTrace]
  refine ⟨31928898704535569889177763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42571864939380759852237017 31928898704535569889177763)
  ·
    refine ⟨47893348056803354833766645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31928898704535569889177763 47893348056803354833766645)
    ·
      refine ⟨4490001380325314515665623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47893348056803354833766645 4490001380325314515665623)
      ·
        refine ⟨6735002070487971773498435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4490001380325314515665623 6735002070487971773498435)
        ·
          refine ⟨10102503105731957660247653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6735002070487971773498435 10102503105731957660247653)
          ·
            refine ⟨1894219332324742061296435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10102503105731957660247653 1894219332324742061296435)
            ·
              refine ⟨2841328998487113091944653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1894219332324742061296435 2841328998487113091944653)
              ·
                refine ⟨1065498374432667409479245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2841328998487113091944653 1065498374432667409479245)
                ·
                  refine ⟨399561890412250278554717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1065498374432667409479245 399561890412250278554717)
                  ·
                    rfl

theorem cell21_1750824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 3, 3].length) (baseStart_1750824 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1750824 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1750824 prefixEnd_1750824 := by exact prefixLift 1750824
  have htrace : WordTrace (prefixWord ++ tailWord_1750824) baseStart_1750824 baseEnd_1750824 := by
    simpa [prefixWord, tailWord_1750824, baseEnd_1750824] using wordTrace_append hprefix tailTrace_1750824
  have hstable : (prefixWord ++ tailWord_1750824).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750824).length < 2 ^ (prefixWord ++ tailWord_1750824).sum := by decide
  have hdescent : baseEnd_1750824 < baseStart_1750824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750835 : List Nat := [1, 1, 1, 2, 7, 2, 7]
def baseStart_1750835 : Nat := 118140960795 + 1750835 * 2 ^ 59
def prefixEnd_1750835 : Nat := 4983230072969 + 3 ^ 40 * 1750835 * 2
def baseEnd_1750835 : Nat := 44396044529124078207929

theorem tailTrace_1750835 : CollatzResearch.WordTrace tailWord_1750835 prefixEnd_1750835 44396044529124078207929 := by
  unfold tailWord_1750835
  simp only [CollatzResearch.WordTrace]
  refine ⟨63858198612031288657005959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42572132408020859104670639 63858198612031288657005959)
  ·
    refine ⟨95787297918046932985508939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63858198612031288657005959 95787297918046932985508939)
    ·
      refine ⟨143680946877070399478263409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95787297918046932985508939 143680946877070399478263409)
      ·
        refine ⟨107760710157802799608697557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143680946877070399478263409 107760710157802799608697557)
        ·
          refine ⟨2525641644323503115828849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 107760710157802799608697557 2525641644323503115828849)
          ·
            refine ⟨1894231233242627336871637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2525641644323503115828849 1894231233242627336871637)
            ·
              refine ⟨44396044529124078207929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1894231233242627336871637 44396044529124078207929)
              ·
                rfl

theorem cell21_1750835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 7].length) (baseStart_1750835 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1750835 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1750835 prefixEnd_1750835 := by exact prefixLift 1750835
  have htrace : WordTrace (prefixWord ++ tailWord_1750835) baseStart_1750835 baseEnd_1750835 := by
    simpa [prefixWord, tailWord_1750835, baseEnd_1750835] using wordTrace_append hprefix tailTrace_1750835
  have hstable : (prefixWord ++ tailWord_1750835).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750835).length < 2 ^ (prefixWord ++ tailWord_1750835).sum := by decide
  have hdescent : baseEnd_1750835 < baseStart_1750835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750841 : List Nat := [1, 2, 1, 7, 1, 1, 3, 2, 3]
def baseStart_1750841 : Nat := 118140960795 + 1750841 * 2 ^ 59
def prefixEnd_1750841 : Nat := 4983230072969 + 3 ^ 40 * 1750841 * 2
def baseEnd_1750841 : Nat := 399565770043862026771349

theorem tailTrace_1750841 : CollatzResearch.WordTrace tailWord_1750841 prefixEnd_1750841 399565770043862026771349 := by
  unfold tailWord_1750841
  simp only [CollatzResearch.WordTrace]
  refine ⟨63858417450009551681724377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42572278300006367787816251 63858417450009551681724377)
  ·
    refine ⟨47893813087507163761293283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63858417450009551681724377 47893813087507163761293283)
    ·
      refine ⟨71840719631260745641939925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47893813087507163761293283 71840719631260745641939925)
      ·
        refine ⟨1683766866357673725982967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 71840719631260745641939925 1683766866357673725982967)
        ·
          refine ⟨2525650299536510588974451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1683766866357673725982967 2525650299536510588974451)
          ·
            refine ⟨3788475449304765883461677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2525650299536510588974451 3788475449304765883461677)
            ·
              refine ⟨1420678293489287206298129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3788475449304765883461677 1420678293489287206298129)
              ·
                refine ⟨1065508720116965404723597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1420678293489287206298129 1065508720116965404723597)
                ·
                  refine ⟨399565770043862026771349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1065508720116965404723597 399565770043862026771349)
                  ·
                    rfl

theorem cell21_1750841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 2, 3].length) (baseStart_1750841 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1750841 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1750841 prefixEnd_1750841 := by exact prefixLift 1750841
  have htrace : WordTrace (prefixWord ++ tailWord_1750841) baseStart_1750841 baseEnd_1750841 := by
    simpa [prefixWord, tailWord_1750841, baseEnd_1750841] using wordTrace_append hprefix tailTrace_1750841
  have hstable : (prefixWord ++ tailWord_1750841).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750841).length < 2 ^ (prefixWord ++ tailWord_1750841).sum := by decide
  have hdescent : baseEnd_1750841 < baseStart_1750841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1750934 : List Nat := [5, 3, 1, 1, 2, 1, 2, 3, 3]
def baseStart_1750934 : Nat := 118140960795 + 1750934 * 2 ^ 59
def prefixEnd_1750934 : Nat := 4983230072969 + 3 ^ 40 * 1750934 * 2
def baseEnd_1750934 : Nat := 399586993910914531721159

theorem tailTrace_1750934 : CollatzResearch.WordTrace tailWord_1750934 prefixEnd_1750934 399586993910914531721159 := by
  unfold tailWord_1750934
  simp only [CollatzResearch.WordTrace]
  refine ⟨3991363089917039285303741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42574539625781752376573237 3991363089917039285303741)
  ·
    refine ⟨1496761158718889731988903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3991363089917039285303741 1496761158718889731988903)
    ·
      refine ⟨2245141738078334597983355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1496761158718889731988903 2245141738078334597983355)
      ·
        refine ⟨3367712607117501896975033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2245141738078334597983355 3367712607117501896975033)
        ·
          refine ⟨2525784455338126422731275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3367712607117501896975033 2525784455338126422731275)
          ·
            refine ⟨3788676683007189634096913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2525784455338126422731275 3788676683007189634096913)
            ·
              refine ⟨2841507512255392225572685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3788676683007189634096913 2841507512255392225572685)
              ·
                refine ⟨1065565317095772084589757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2841507512255392225572685 1065565317095772084589757)
                ·
                  refine ⟨399586993910914531721159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1065565317095772084589757 399586993910914531721159)
                  ·
                    rfl

theorem cell21_1750934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_1750934 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1750934 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1750934 prefixEnd_1750934 := by exact prefixLift 1750934
  have htrace : WordTrace (prefixWord ++ tailWord_1750934) baseStart_1750934 baseEnd_1750934 := by
    simpa [prefixWord, tailWord_1750934, baseEnd_1750934] using wordTrace_append hprefix tailTrace_1750934
  have hstable : (prefixWord ++ tailWord_1750934).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1750934).length < 2 ^ (prefixWord ++ tailWord_1750934).sum := by decide
  have hdescent : baseEnd_1750934 < baseStart_1750934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1750934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751063 : List Nat := [1, 1, 3, 5, 3, 8]
def baseStart_1751063 : Nat := 118140960795 + 1751063 * 2 ^ 59
def prefixEnd_1751063 : Nat := 4983230072969 + 3 ^ 40 * 1751063 * 2
def baseEnd_1751063 : Nat := 14800608646979221261885

theorem tailTrace_1751063 : CollatzResearch.WordTrace tailWord_1751063 prefixEnd_1751063 14800608646979221261885 := by
  unfold tailWord_1751063
  simp only [CollatzResearch.WordTrace]
  refine ⟨63866514455205283596305843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42577676303470189064203895 63866514455205283596305843)
  ·
    refine ⟨95799771682807925394458765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63866514455205283596305843 95799771682807925394458765)
    ·
      refine ⟨35924914381052972022922037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95799771682807925394458765 35924914381052972022922037)
      ·
        refine ⟨3367960723223716127148941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35924914381052972022922037 3367960723223716127148941)
        ·
          refine ⟨1262985271208893547680853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3367960723223716127148941 1262985271208893547680853)
          ·
            refine ⟨14800608646979221261885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1262985271208893547680853 14800608646979221261885)
            ·
              rfl

theorem cell21_1751063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 8].length) (baseStart_1751063 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1751063 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1751063 prefixEnd_1751063 := by exact prefixLift 1751063
  have htrace : WordTrace (prefixWord ++ tailWord_1751063) baseStart_1751063 baseEnd_1751063 := by
    simpa [prefixWord, tailWord_1751063, baseEnd_1751063] using wordTrace_append hprefix tailTrace_1751063
  have hstable : (prefixWord ++ tailWord_1751063).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751063).length < 2 ^ (prefixWord ++ tailWord_1751063).sum := by decide
  have hdescent : baseEnd_1751063 < baseStart_1751063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751094 : List Nat := [5, 1, 2, 1, 1, 1, 3, 2, 5]
def baseStart_1751094 : Nat := 118140960795 + 1751094 * 2 ^ 59
def prefixEnd_1751094 : Nat := 4983230072969 + 3 ^ 40 * 1751094 * 2
def baseEnd_1751094 : Nat := 399623508090789809054165

theorem tailTrace_1751094 : CollatzResearch.WordTrace tailWord_1751094 prefixEnd_1751094 399623508090789809054165 := by
  unfold tailWord_1751094
  simp only [CollatzResearch.WordTrace]
  refine ⟨3991727819880810993167771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42578430078728650593789557 3991727819880810993167771)
  ·
    refine ⟨5987591729821216489751657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3991727819880810993167771 5987591729821216489751657)
    ·
      refine ⟨4490693797365912367313743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5987591729821216489751657 4490693797365912367313743)
      ·
        refine ⟨6736040696048868550970615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4490693797365912367313743 6736040696048868550970615)
        ·
          refine ⟨10104061044073302826455923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6736040696048868550970615 10104061044073302826455923)
          ·
            refine ⟨15156091566109954239683885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10104061044073302826455923 15156091566109954239683885)
            ·
              refine ⟨5683534337291232839881457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15156091566109954239683885 5683534337291232839881457)
              ·
                refine ⟨4262650752968424629911093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5683534337291232839881457 4262650752968424629911093)
                ·
                  refine ⟨399623508090789809054165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4262650752968424629911093 399623508090789809054165)
                  ·
                    rfl

theorem cell21_1751094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_1751094 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1751094 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1751094 prefixEnd_1751094 := by exact prefixLift 1751094
  have htrace : WordTrace (prefixWord ++ tailWord_1751094) baseStart_1751094 baseEnd_1751094 := by
    simpa [prefixWord, tailWord_1751094, baseEnd_1751094] using wordTrace_append hprefix tailTrace_1751094
  have hstable : (prefixWord ++ tailWord_1751094).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751094).length < 2 ^ (prefixWord ++ tailWord_1751094).sum := by decide
  have hdescent : baseEnd_1751094 < baseStart_1751094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751125 : List Nat := [1, 3, 2, 2, 1, 5, 1, 2, 4]
def baseStart_1751125 : Nat := 118140960795 + 1751125 * 2 ^ 59
def prefixEnd_1751125 : Nat := 4983230072969 + 3 ^ 40 * 1751125 * 2
def baseEnd_1751125 : Nat := 399630582713140644037435

theorem tailTrace_1751125 : CollatzResearch.WordTrace tailWord_1751125 prefixEnd_1751125 399630582713140644037435 := by
  unfold tailWord_1751125
  simp only [CollatzResearch.WordTrace]
  refine ⟨63868775780980668185062829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42579183853987112123375219 63868775780980668185062829)
  ·
    refine ⟨23950790917867750569398561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63868775780980668185062829 23950790917867750569398561)
    ·
      refine ⟨17963093188400812927048921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23950790917867750569398561 17963093188400812927048921)
      ·
        refine ⟨13472319891300609695286691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17963093188400812927048921 13472319891300609695286691)
        ·
          refine ⟨20208479836950914542930037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13472319891300609695286691 20208479836950914542930037)
          ·
            refine ⟨1894544984714148238399691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20208479836950914542930037 1894544984714148238399691)
            ·
              refine ⟨2841817477071222357599537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1894544984714148238399691 2841817477071222357599537)
              ·
                refine ⟨2131363107803416768199653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2841817477071222357599537 2131363107803416768199653)
                ·
                  refine ⟨399630582713140644037435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2131363107803416768199653 399630582713140644037435)
                  ·
                    rfl

theorem cell21_1751125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 2, 4].length) (baseStart_1751125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1751125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1751125 prefixEnd_1751125 := by exact prefixLift 1751125
  have htrace : WordTrace (prefixWord ++ tailWord_1751125) baseStart_1751125 baseEnd_1751125 := by
    simpa [prefixWord, tailWord_1751125, baseEnd_1751125] using wordTrace_append hprefix tailTrace_1751125
  have hstable : (prefixWord ++ tailWord_1751125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751125).length < 2 ^ (prefixWord ++ tailWord_1751125).sum := by decide
  have hdescent : baseEnd_1751125 < baseStart_1751125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751201 : List Nat := [1, 2, 3, 3, 1, 2, 4, 1, 4]
def baseStart_1751201 : Nat := 118140960795 + 1751201 * 2 ^ 59
def prefixEnd_1751201 : Nat := 4983230072969 + 3 ^ 40 * 1751201 * 2
def baseEnd_1751201 : Nat := 399647926948581400770613

theorem tailTrace_1751201 : CollatzResearch.WordTrace tailWord_1751201 prefixEnd_1751201 399647926948581400770613 := by
  unfold tailWord_1751201
  simp only [CollatzResearch.WordTrace]
  refine ⟨63871547728705333164829457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42581031819136888776552971 63871547728705333164829457)
  ·
    refine ⟨47903660796528999873622093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63871547728705333164829457 47903660796528999873622093)
    ·
      refine ⟨17963872798698374952608285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47903660796528999873622093 17963872798698374952608285)
      ·
        refine ⟨6736452299511890607228107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17963872798698374952608285 6736452299511890607228107)
        ·
          refine ⟨10104678449267835910842161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6736452299511890607228107 10104678449267835910842161)
          ·
            refine ⟨7578508836950876933131621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10104678449267835910842161 7578508836950876933131621)
            ·
              refine ⟨1420970406928289424962179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7578508836950876933131621 1420970406928289424962179)
              ·
                refine ⟨2131455610392434137443269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1420970406928289424962179 2131455610392434137443269)
                ·
                  refine ⟨399647926948581400770613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2131455610392434137443269 399647926948581400770613)
                  ·
                    rfl

theorem cell21_1751201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 1, 4].length) (baseStart_1751201 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1751201 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1751201 prefixEnd_1751201 := by exact prefixLift 1751201
  have htrace : WordTrace (prefixWord ++ tailWord_1751201) baseStart_1751201 baseEnd_1751201 := by
    simpa [prefixWord, tailWord_1751201, baseEnd_1751201] using wordTrace_append hprefix tailTrace_1751201
  have hstable : (prefixWord ++ tailWord_1751201).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751201).length < 2 ^ (prefixWord ++ tailWord_1751201).sum := by decide
  have hdescent : baseEnd_1751201 < baseStart_1751201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751266 : List Nat := [3, 3, 4, 1, 1, 1, 3, 5]
def baseStart_1751266 : Nat := 118140960795 + 1751266 * 2 ^ 59
def prefixEnd_1751266 : Nat := 4983230072969 + 3 ^ 40 * 1751266 * 2
def baseEnd_1751266 : Nat := 133220920278051910729049

theorem tailTrace_1751266 : CollatzResearch.WordTrace tailWord_1751266 prefixEnd_1751266 133220920278051910729049 := by
  unfold tailWord_1751266
  simp only [CollatzResearch.WordTrace]
  refine ⟨15968479618367462316486413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42582612315646566177297101 15968479618367462316486413)
  ·
    refine ⟨5988179856887798368682405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15968479618367462316486413 5988179856887798368682405)
    ·
      refine ⟨1122783723166462194127951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5988179856887798368682405 1122783723166462194127951)
      ·
        refine ⟨1684175584749693291191927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1122783723166462194127951 1684175584749693291191927)
        ·
          refine ⟨2526263377124539936787891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1684175584749693291191927 2526263377124539936787891)
          ·
            refine ⟨3789395065686809905181837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2526263377124539936787891 3789395065686809905181837)
            ·
              refine ⟨1421023149632553714443189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3789395065686809905181837 1421023149632553714443189)
              ·
                refine ⟨133220920278051910729049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1421023149632553714443189 133220920278051910729049)
                ·
                  rfl

theorem cell21_1751266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 5].length) (baseStart_1751266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1751266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1751266 prefixEnd_1751266 := by exact prefixLift 1751266
  have htrace : WordTrace (prefixWord ++ tailWord_1751266) baseStart_1751266 baseEnd_1751266 := by
    simpa [prefixWord, tailWord_1751266, baseEnd_1751266] using wordTrace_append hprefix tailTrace_1751266
  have hstable : (prefixWord ++ tailWord_1751266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751266).length < 2 ^ (prefixWord ++ tailWord_1751266).sum := by decide
  have hdescent : baseEnd_1751266 < baseStart_1751266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751305 : List Nat := [1, 2, 1, 1, 3, 5, 2, 1, 5]
def baseStart_1751305 : Nat := 118140960795 + 1751305 * 2 ^ 59
def prefixEnd_1751305 : Nat := 4983230072969 + 3 ^ 40 * 1751305 * 2
def baseEnd_1751305 : Nat := 399671661165500331037067

theorem tailTrace_1751305 : CollatzResearch.WordTrace tailWord_1751305 prefixEnd_1751305 399671661165500331037067 := by
  unfold tailWord_1751305
  simp only [CollatzResearch.WordTrace]
  refine ⟨63875340920328558926615369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42583560613552372617743579 63875340920328558926615369)
  ·
    refine ⟨47906505690246419194961527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63875340920328558926615369 47906505690246419194961527)
    ·
      refine ⟨71859758535369628792442291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47906505690246419194961527 71859758535369628792442291)
      ·
        refine ⟨107789637803054443188663437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71859758535369628792442291 107789637803054443188663437)
        ·
          refine ⟨40421114176145416195748789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107789637803054443188663437 40421114176145416195748789)
          ·
            refine ⟨3789479454013632768351449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40421114176145416195748789 3789479454013632768351449)
            ·
              refine ⟨2842109590510224576263587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3789479454013632768351449 2842109590510224576263587)
              ·
                refine ⟨4263164385765336864395381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2842109590510224576263587 4263164385765336864395381)
                ·
                  refine ⟨399671661165500331037067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4263164385765336864395381 399671661165500331037067)
                  ·
                    rfl

theorem cell21_1751305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 5].length) (baseStart_1751305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1751305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1751305 prefixEnd_1751305 := by exact prefixLift 1751305
  have htrace : WordTrace (prefixWord ++ tailWord_1751305) baseStart_1751305 baseEnd_1751305 := by
    simpa [prefixWord, tailWord_1751305, baseEnd_1751305] using wordTrace_append hprefix tailTrace_1751305
  have hstable : (prefixWord ++ tailWord_1751305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751305).length < 2 ^ (prefixWord ++ tailWord_1751305).sum := by decide
  have hdescent : baseEnd_1751305 < baseStart_1751305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751325 : List Nat := [1, 4, 2, 3, 3, 1, 2, 5]
def baseStart_1751325 : Nat := 118140960795 + 1751325 * 2 ^ 59
def prefixEnd_1751325 : Nat := 4983230072969 + 3 ^ 40 * 1751325 * 2
def baseEnd_1751325 : Nat := 133225408479328246901231

theorem tailTrace_1751325 : CollatzResearch.WordTrace tailWord_1751325 prefixEnd_1751325 133225408479328246901231 := by
  unfold tailWord_1751325
  simp only [CollatzResearch.WordTrace]
  refine ⟨63876070380256102342343429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42584046920170734894895619 63876070380256102342343429)
  ·
    refine ⟨11976763196298019189189393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63876070380256102342343429 11976763196298019189189393)
    ·
      refine ⟨8982572397223514391892045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11976763196298019189189393 8982572397223514391892045)
      ·
        refine ⟨3368464648958817896959517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8982572397223514391892045 3368464648958817896959517)
        ·
          refine ⟨1263174243359556711359819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3368464648958817896959517 1263174243359556711359819)
          ·
            refine ⟨1894761365039335067039729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1263174243359556711359819 1894761365039335067039729)
            ·
              refine ⟨1421071023779501300279797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1894761365039335067039729 1421071023779501300279797)
              ·
                refine ⟨133225408479328246901231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1421071023779501300279797 133225408479328246901231)
                ·
                  rfl

theorem cell21_1751325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 5].length) (baseStart_1751325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1751325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1751325 prefixEnd_1751325 := by exact prefixLift 1751325
  have htrace : WordTrace (prefixWord ++ tailWord_1751325) baseStart_1751325 baseEnd_1751325 := by
    simpa [prefixWord, tailWord_1751325, baseEnd_1751325] using wordTrace_append hprefix tailTrace_1751325
  have hstable : (prefixWord ++ tailWord_1751325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751325).length < 2 ^ (prefixWord ++ tailWord_1751325).sum := by decide
  have hdescent : baseEnd_1751325 < baseStart_1751325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751584 : List Nat := [2, 1, 1, 6, 2, 2, 2, 2, 3]
def baseStart_1751584 : Nat := 118140960795 + 1751584 * 2 ^ 59
def prefixEnd_1751584 : Nat := 4983230072969 + 3 ^ 40 * 1751584 * 2
def baseEnd_1751584 : Nat := 399735332766657845886497

theorem tailTrace_1751584 : CollatzResearch.WordTrace tailWord_1751584 prefixEnd_1751584 399735332766657845886497 := by
  unfold tailWord_1751584
  simp only [CollatzResearch.WordTrace]
  refine ⟨31942758443158894788010903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42590344590878526384014537 31942758443158894788010903)
  ·
    refine ⟨47914137664738342182016355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31942758443158894788010903 47914137664738342182016355)
    ·
      refine ⟨71871206497107513273024533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47914137664738342182016355 71871206497107513273024533)
      ·
        refine ⟨3368962804551914684673025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 71871206497107513273024533 3368962804551914684673025)
        ·
          refine ⟨2526722103413936013504769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3368962804551914684673025 2526722103413936013504769)
          ·
            refine ⟨1895041577560452010128577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2526722103413936013504769 1895041577560452010128577)
            ·
              refine ⟨1421281183170339007596433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1895041577560452010128577 1421281183170339007596433)
              ·
                refine ⟨1065960887377754255697325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1421281183170339007596433 1065960887377754255697325)
                ·
                  refine ⟨399735332766657845886497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1065960887377754255697325 399735332766657845886497)
                  ·
                    rfl

theorem cell21_1751584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 2, 3].length) (baseStart_1751584 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1751584 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1751584 prefixEnd_1751584 := by exact prefixLift 1751584
  have htrace : WordTrace (prefixWord ++ tailWord_1751584) baseStart_1751584 baseEnd_1751584 := by
    simpa [prefixWord, tailWord_1751584, baseEnd_1751584] using wordTrace_append hprefix tailTrace_1751584
  have hstable : (prefixWord ++ tailWord_1751584).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751584).length < 2 ^ (prefixWord ++ tailWord_1751584).sum := by decide
  have hdescent : baseEnd_1751584 < baseStart_1751584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751626 : List Nat := [3, 1, 2, 1, 1, 5, 2, 3, 3]
def baseStart_1751626 : Nat := 118140960795 + 1751626 * 2 ^ 59
def prefixEnd_1751626 : Nat := 4983230072969 + 3 ^ 40 * 1751626 * 2
def baseEnd_1751626 : Nat := 399744917738875106186411

theorem tailTrace_1751626 : CollatzResearch.WordTrace tailWord_1751626 prefixEnd_1751626 399744917738875106186411 := by
  unfold tailWord_1751626
  simp only [CollatzResearch.WordTrace]
  refine ⟨15971762188041407687262683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42591365834777087166033821 15971762188041407687262683)
  ·
    refine ⟨23957643282062111530894025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15971762188041407687262683 23957643282062111530894025)
    ·
      refine ⟨17968232461546583648170519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23957643282062111530894025 17968232461546583648170519)
      ·
        refine ⟨26952348692319875472255779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17968232461546583648170519 26952348692319875472255779)
        ·
          refine ⟨40428523038479813208383669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26952348692319875472255779 40428523038479813208383669)
          ·
            refine ⟨3790174034857482488285969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40428523038479813208383669 3790174034857482488285969)
            ·
              refine ⟨2842630526143111866214477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3790174034857482488285969 2842630526143111866214477)
              ·
                refine ⟨1065986447303666949830429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2842630526143111866214477 1065986447303666949830429)
                ·
                  refine ⟨399744917738875106186411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1065986447303666949830429 399744917738875106186411)
                  ·
                    rfl

theorem cell21_1751626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 3, 3].length) (baseStart_1751626 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1751626 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1751626 prefixEnd_1751626 := by exact prefixLift 1751626
  have htrace : WordTrace (prefixWord ++ tailWord_1751626) baseStart_1751626 baseEnd_1751626 := by
    simpa [prefixWord, tailWord_1751626, baseEnd_1751626] using wordTrace_append hprefix tailTrace_1751626
  have hstable : (prefixWord ++ tailWord_1751626).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751626).length < 2 ^ (prefixWord ++ tailWord_1751626).sum := by decide
  have hdescent : baseEnd_1751626 < baseStart_1751626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751761 : List Nat := [1, 2, 2, 1, 2, 3, 3, 4, 3]
def baseStart_1751761 : Nat := 118140960795 + 1751761 * 2 ^ 59
def prefixEnd_1751761 : Nat := 4983230072969 + 3 ^ 40 * 1751761 * 2
def baseEnd_1751761 : Nat := 399775726578144871436135

theorem tailTrace_1751761 : CollatzResearch.WordTrace tailWord_1751761 prefixEnd_1751761 399775726578144871436135 := by
  unfold tailWord_1751761
  simp only [CollatzResearch.WordTrace]
  refine ⟨63891972606676548805215137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42594648404451032536810091 63891972606676548805215137)
  ·
    refine ⟨47918979455007411603911353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63891972606676548805215137 47918979455007411603911353)
    ·
      refine ⟨35939234591255558702933515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47918979455007411603911353 35939234591255558702933515)
      ·
        refine ⟨53908851886883338054400273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35939234591255558702933515 53908851886883338054400273)
        ·
          refine ⟨40431638915162503540800205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53908851886883338054400273 40431638915162503540800205)
          ·
            refine ⟨15161864593185938827800077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40431638915162503540800205 15161864593185938827800077)
            ·
              refine ⟨5685699222444727060425029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15161864593185938827800077 5685699222444727060425029)
              ·
                refine ⟨1066068604208386323829693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5685699222444727060425029 1066068604208386323829693)
                ·
                  refine ⟨399775726578144871436135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1066068604208386323829693 399775726578144871436135)
                  ·
                    rfl

theorem cell21_1751761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 4, 3].length) (baseStart_1751761 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1751761 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1751761 prefixEnd_1751761 := by exact prefixLift 1751761
  have htrace : WordTrace (prefixWord ++ tailWord_1751761) baseStart_1751761 baseEnd_1751761 := by
    simpa [prefixWord, tailWord_1751761, baseEnd_1751761] using wordTrace_append hprefix tailTrace_1751761
  have hstable : (prefixWord ++ tailWord_1751761).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751761).length < 2 ^ (prefixWord ++ tailWord_1751761).sum := by decide
  have hdescent : baseEnd_1751761 < baseStart_1751761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751764 : List Nat := [2, 4, 1, 3, 3, 1, 1, 6]
def baseStart_1751764 : Nat := 118140960795 + 1751764 * 2 ^ 59
def prefixEnd_1751764 : Nat := 4983230072969 + 3 ^ 40 * 1751764 * 2
def baseEnd_1751764 : Nat := 133258803739672510962043

theorem tailTrace_1751764 : CollatzResearch.WordTrace tailWord_1751764 prefixEnd_1751764 133258803739672510962043 := by
  unfold tailWord_1751764
  simp only [CollatzResearch.WordTrace]
  refine ⟨31946041012832840158787173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42594721350443786878382897 31946041012832840158787173)
  ·
    refine ⟨5989882689906157529772595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31946041012832840158787173 5989882689906157529772595)
    ·
      refine ⟨8984824034859236294658893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5989882689906157529772595 8984824034859236294658893)
      ·
        refine ⟨3369309013072213610497085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8984824034859236294658893 3369309013072213610497085)
        ·
          refine ⟨1263490879902080103936407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3369309013072213610497085 1263490879902080103936407)
          ·
            refine ⟨1895236319853120155904611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1263490879902080103936407 1895236319853120155904611)
            ·
              refine ⟨2842854479779680233856917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1895236319853120155904611 2842854479779680233856917)
              ·
                refine ⟨133258803739672510962043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2842854479779680233856917 133258803739672510962043)
                ·
                  rfl

theorem cell21_1751764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 6].length) (baseStart_1751764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1751764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1751764 prefixEnd_1751764 := by exact prefixLift 1751764
  have htrace : WordTrace (prefixWord ++ tailWord_1751764) baseStart_1751764 baseEnd_1751764 := by
    simpa [prefixWord, tailWord_1751764, baseEnd_1751764] using wordTrace_append hprefix tailTrace_1751764
  have hstable : (prefixWord ++ tailWord_1751764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751764).length < 2 ^ (prefixWord ++ tailWord_1751764).sum := by decide
  have hdescent : baseEnd_1751764 < baseStart_1751764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751775 : List Nat := [1, 1, 2, 3, 2, 3, 2, 3, 4]
def baseStart_1751775 : Nat := 118140960795 + 1751775 * 2 ^ 59
def prefixEnd_1751775 : Nat := 4983230072969 + 3 ^ 40 * 1751775 * 2
def baseEnd_1751775 : Nat := 399778921568883958202773

theorem tailTrace_1751775 : CollatzResearch.WordTrace tailWord_1751775 prefixEnd_1751775 399778921568883958202773 := by
  unfold tailWord_1751775
  simp only [CollatzResearch.WordTrace]
  refine ⟨63892483228625829196224779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42594988819083886130816519 63892483228625829196224779)
  ·
    refine ⟨95838724842938743794337169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63892483228625829196224779 95838724842938743794337169)
    ·
      refine ⟨71879043632204057845752877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95838724842938743794337169 71879043632204057845752877)
      ·
        refine ⟨26954641362076521692157329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71879043632204057845752877 26954641362076521692157329)
        ·
          refine ⟨20215981021557391269117997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26954641362076521692157329 20215981021557391269117997)
          ·
            refine ⟨7580992883084021725919249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20215981021557391269117997 7580992883084021725919249)
            ·
              refine ⟨5685744662313016294439437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7580992883084021725919249 5685744662313016294439437)
              ·
                refine ⟨2132154248367381110414789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5685744662313016294439437 2132154248367381110414789)
                ·
                  refine ⟨399778921568883958202773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2132154248367381110414789 399778921568883958202773)
                  ·
                    rfl

theorem cell21_1751775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 3, 4].length) (baseStart_1751775 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1751775 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1751775 prefixEnd_1751775 := by exact prefixLift 1751775
  have htrace : WordTrace (prefixWord ++ tailWord_1751775) baseStart_1751775 baseEnd_1751775 := by
    simpa [prefixWord, tailWord_1751775, baseEnd_1751775] using wordTrace_append hprefix tailTrace_1751775
  have hstable : (prefixWord ++ tailWord_1751775).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751775).length < 2 ^ (prefixWord ++ tailWord_1751775).sum := by decide
  have hdescent : baseEnd_1751775 < baseStart_1751775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751806 : List Nat := [4, 2, 2, 1, 2, 2, 8]
def baseStart_1751806 : Nat := 118140960795 + 1751806 * 2 ^ 59
def prefixEnd_1751806 : Nat := 4983230072969 + 3 ^ 40 * 1751806 * 2
def baseEnd_1751806 : Nat := 44420666243470532576227

theorem tailTrace_1751806 : CollatzResearch.WordTrace tailWord_1751806 prefixEnd_1751806 44420666243470532576227 := by
  unfold tailWord_1751806
  simp only [CollatzResearch.WordTrace]
  refine ⟨7986701736439190186325409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42595742594342347660402181 7986701736439190186325409)
  ·
    refine ⟨5990026302329392639744057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7986701736439190186325409 5990026302329392639744057)
    ·
      refine ⟨4492519726747044479808043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5990026302329392639744057 4492519726747044479808043)
      ·
        refine ⟨6738779590120566719712065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4492519726747044479808043 6738779590120566719712065)
        ·
          refine ⟨5054084692590425039784049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6738779590120566719712065 5054084692590425039784049)
          ·
            refine ⟨3790563519442818779838037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5054084692590425039784049 3790563519442818779838037)
            ·
              refine ⟨44420666243470532576227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3790563519442818779838037 44420666243470532576227)
              ·
                rfl

theorem cell21_1751806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 8].length) (baseStart_1751806 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1751806 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1751806 prefixEnd_1751806 := by exact prefixLift 1751806
  have htrace : WordTrace (prefixWord ++ tailWord_1751806) baseStart_1751806 baseEnd_1751806 := by
    simpa [prefixWord, tailWord_1751806, baseEnd_1751806] using wordTrace_append hprefix tailTrace_1751806
  have hstable : (prefixWord ++ tailWord_1751806).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751806).length < 2 ^ (prefixWord ++ tailWord_1751806).sum := by decide
  have hdescent : baseEnd_1751806 < baseStart_1751806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751826 : List Nat := [3, 2, 4, 1, 2, 1, 3, 1, 4]
def baseStart_1751826 : Nat := 118140960795 + 1751826 * 2 ^ 59
def prefixEnd_1751826 : Nat := 4983230072969 + 3 ^ 40 * 1751826 * 2
def baseEnd_1751826 : Nat := 399790560463719202852669

theorem tailTrace_1751826 : CollatzResearch.WordTrace tailWord_1751826 prefixEnd_1751826 399790560463719202852669 := by
  unfold tailWord_1751826
  simp only [CollatzResearch.WordTrace]
  refine ⟨15973585837860266226582833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42596228900960709937554221 15973585837860266226582833)
  ·
    refine ⟨11980189378395199669937125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15973585837860266226582833 11980189378395199669937125)
    ·
      refine ⟨2246285508449099938113211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11980189378395199669937125 2246285508449099938113211)
      ·
        refine ⟨3369428262673649907169817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2246285508449099938113211 3369428262673649907169817)
        ·
          refine ⟨2527071197005237430377363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3369428262673649907169817 2527071197005237430377363)
          ·
            refine ⟨3790606795507856145566045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2527071197005237430377363 3790606795507856145566045)
            ·
              refine ⟨1421477548315446054587267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3790606795507856145566045 1421477548315446054587267)
              ·
                refine ⟨2132216322473169081880901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1421477548315446054587267 2132216322473169081880901)
                ·
                  refine ⟨399790560463719202852669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2132216322473169081880901 399790560463719202852669)
                  ·
                    rfl

theorem cell21_1751826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_1751826 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1751826 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1751826 prefixEnd_1751826 := by exact prefixLift 1751826
  have htrace : WordTrace (prefixWord ++ tailWord_1751826) baseStart_1751826 baseEnd_1751826 := by
    simpa [prefixWord, tailWord_1751826, baseEnd_1751826] using wordTrace_append hprefix tailTrace_1751826
  have hstable : (prefixWord ++ tailWord_1751826).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751826).length < 2 ^ (prefixWord ++ tailWord_1751826).sum := by decide
  have hdescent : baseEnd_1751826 < baseStart_1751826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751885 : List Nat := [1, 6, 1, 2, 2, 1, 1, 3, 4]
def baseStart_1751885 : Nat := 118140960795 + 1751885 * 2 ^ 59
def prefixEnd_1751885 : Nat := 4983230072969 + 3 ^ 40 * 1751885 * 2
def baseEnd_1751885 : Nat := 399804025067548211369215

theorem tailTrace_1751885 : CollatzResearch.WordTrace tailWord_1751885 prefixEnd_1751885 399804025067548211369215 := by
  unfold tailWord_1751885
  simp only [CollatzResearch.WordTrace]
  refine ⟨63896495258227317982729109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42597663505484878655152739 63896495258227317982729109)
  ·
    refine ⟨2995148215229405530440427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 63896495258227317982729109 2995148215229405530440427)
    ·
      refine ⟨4492722322844108295660641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2995148215229405530440427 4492722322844108295660641)
      ·
        refine ⟨3369541742133081221745481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4492722322844108295660641 3369541742133081221745481)
        ·
          refine ⟨2527156306599810916309111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3369541742133081221745481 2527156306599810916309111)
          ·
            refine ⟨3790734459899716374463667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2527156306599810916309111 3790734459899716374463667)
            ·
              refine ⟨5686101689849574561695501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3790734459899716374463667 5686101689849574561695501)
              ·
                refine ⟨2132288133693590460635813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5686101689849574561695501 2132288133693590460635813)
                ·
                  refine ⟨399804025067548211369215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2132288133693590460635813 399804025067548211369215)
                  ·
                    rfl

theorem cell21_1751885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_1751885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1751885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1751885 prefixEnd_1751885 := by exact prefixLift 1751885
  have htrace : WordTrace (prefixWord ++ tailWord_1751885) baseStart_1751885 baseEnd_1751885 := by
    simpa [prefixWord, tailWord_1751885, baseEnd_1751885] using wordTrace_append hprefix tailTrace_1751885
  have hstable : (prefixWord ++ tailWord_1751885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751885).length < 2 ^ (prefixWord ++ tailWord_1751885).sum := by decide
  have hdescent : baseEnd_1751885 < baseStart_1751885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751924 : List Nat := [2, 19]
def baseStart_1751924 : Nat := 118140960795 + 1751924 * 2 ^ 59
def prefixEnd_1751924 : Nat := 4983230072969 + 3 ^ 40 * 1751924 * 2
def baseEnd_1751924 : Nat := 182813408961542208605

theorem tailTrace_1751924 : CollatzResearch.WordTrace tailWord_1751924 prefixEnd_1751924 182813408961542208605 := by
  unfold tailWord_1751924
  simp only [CollatzResearch.WordTrace]
  refine ⟨31948958852543013821699413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42598611803390685095599217 31948958852543013821699413)
  ·
    refine ⟨182813408961542208605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 19 31948958852543013821699413 182813408961542208605)
    ·
      rfl

theorem cell21_1751924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 19].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 19].length) (baseStart_1751924 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1751924 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1751924 prefixEnd_1751924 := by exact prefixLift 1751924
  have htrace : WordTrace (prefixWord ++ tailWord_1751924) baseStart_1751924 baseEnd_1751924 := by
    simpa [prefixWord, tailWord_1751924, baseEnd_1751924] using wordTrace_append hprefix tailTrace_1751924
  have hstable : (prefixWord ++ tailWord_1751924).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751924).length < 2 ^ (prefixWord ++ tailWord_1751924).sum := by decide
  have hdescent : baseEnd_1751924 < baseStart_1751924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751941 : List Nat := [1, 3, 1, 1, 3, 3, 3, 6]
def baseStart_1751941 : Nat := 118140960795 + 1751941 * 2 ^ 59
def prefixEnd_1751941 : Nat := 4983230072969 + 3 ^ 40 * 1751941 * 2
def baseEnd_1751941 : Nat := 133272268343501519478589

theorem tailTrace_1751941 : CollatzResearch.WordTrace tailWord_1751941 prefixEnd_1751941 133272268343501519478589 := by
  unfold tailWord_1751941
  simp only [CollatzResearch.WordTrace]
  refine ⟨63898537746024439546767677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42599025164016293031178451 63898537746024439546767677)
  ·
    refine ⟨23961951654759164830037879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63898537746024439546767677 23961951654759164830037879)
    ·
      refine ⟨35942927482138747245056819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23961951654759164830037879 35942927482138747245056819)
      ·
        refine ⟨53914391223208120867585229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35942927482138747245056819 53914391223208120867585229)
        ·
          refine ⟨20217896708703045325344461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53914391223208120867585229 20217896708703045325344461)
          ·
            refine ⟨7581711265763641997004173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20217896708703045325344461 7581711265763641997004173)
            ·
              refine ⟨2843141724661365748876565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7581711265763641997004173 2843141724661365748876565)
              ·
                refine ⟨133272268343501519478589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2843141724661365748876565 133272268343501519478589)
                ·
                  rfl

theorem cell21_1751941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 6].length) (baseStart_1751941 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1751941 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1751941 prefixEnd_1751941 := by exact prefixLift 1751941
  have htrace : WordTrace (prefixWord ++ tailWord_1751941) baseStart_1751941 baseEnd_1751941 := by
    simpa [prefixWord, tailWord_1751941, baseEnd_1751941] using wordTrace_append hprefix tailTrace_1751941
  have hstable : (prefixWord ++ tailWord_1751941).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751941).length < 2 ^ (prefixWord ++ tailWord_1751941).sum := by decide
  have hdescent : baseEnd_1751941 < baseStart_1751941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1751989 : List Nat := [1, 3, 3, 2, 1, 1, 1, 6, 3]
def baseStart_1751989 : Nat := 118140960795 + 1751989 * 2 ^ 59
def prefixEnd_1751989 : Nat := 4983230072969 + 3 ^ 40 * 1751989 * 2
def baseEnd_1751989 : Nat := 399827759284467141635669

theorem tailTrace_1751989 : CollatzResearch.WordTrace tailWord_1751989 prefixEnd_1751989 399827759284467141635669 := by
  unfold tailWord_1751989
  simp only [CollatzResearch.WordTrace]
  refine ⟨63900288449850543744515021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42600192299900362496343347 63900288449850543744515021)
  ·
    refine ⟨23962608168693953904193133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63900288449850543744515021 23962608168693953904193133)
    ·
      refine ⟨8985978063260232714072425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23962608168693953904193133 8985978063260232714072425)
      ·
        refine ⟨6739483547445174535554319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8985978063260232714072425 6739483547445174535554319)
        ·
          refine ⟨10109225321167761803331479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6739483547445174535554319 10109225321167761803331479)
          ·
            refine ⟨15163837981751642704997219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10109225321167761803331479 15163837981751642704997219)
            ·
              refine ⟨22745756972627464057495829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15163837981751642704997219 22745756972627464057495829)
              ·
                refine ⟨1066207358091912377695117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22745756972627464057495829 1066207358091912377695117)
                ·
                  refine ⟨399827759284467141635669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1066207358091912377695117 399827759284467141635669)
                  ·
                    rfl

theorem cell21_1751989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 6, 3].length) (baseStart_1751989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1751989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1751989 prefixEnd_1751989 := by exact prefixLift 1751989
  have htrace : WordTrace (prefixWord ++ tailWord_1751989) baseStart_1751989 baseEnd_1751989 := by
    simpa [prefixWord, tailWord_1751989, baseEnd_1751989] using wordTrace_append hprefix tailTrace_1751989
  have hstable : (prefixWord ++ tailWord_1751989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1751989).length < 2 ^ (prefixWord ++ tailWord_1751989).sum := by decide
  have hdescent : baseEnd_1751989 < baseStart_1751989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1751989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752034 : List Nat := [3, 3, 3, 1, 1, 1, 9]
def baseStart_1752034 : Nat := 118140960795 + 1752034 * 2 ^ 59
def prefixEnd_1752034 : Nat := 4983230072969 + 3 ^ 40 * 1752034 * 2
def baseEnd_1752034 : Nat := 44426447655284118153953

theorem tailTrace_1752034 : CollatzResearch.WordTrace tailWord_1752034 prefixEnd_1752034 44426447655284118153953 := by
  unfold tailWord_1752034
  simp only [CollatzResearch.WordTrace]
  refine ⟨15975482433671879107475789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42601286489791677619935437 15975482433671879107475789)
  ·
    refine ⟨5990805912626954665303421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15975482433671879107475789 5990805912626954665303421)
    ·
      refine ⟨2246552217235107999488783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5990805912626954665303421 2246552217235107999488783)
      ·
        refine ⟨3369828325852661999233175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2246552217235107999488783 3369828325852661999233175)
        ·
          refine ⟨5054742488778992998849763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3369828325852661999233175 5054742488778992998849763)
          ·
            refine ⟨7582113733168489498274645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5054742488778992998849763 7582113733168489498274645)
            ·
              refine ⟨44426447655284118153953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7582113733168489498274645 44426447655284118153953)
              ·
                rfl

theorem cell21_1752034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 9].length) (baseStart_1752034 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1752034 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1752034 prefixEnd_1752034 := by exact prefixLift 1752034
  have htrace : WordTrace (prefixWord ++ tailWord_1752034) baseStart_1752034 baseEnd_1752034 := by
    simpa [prefixWord, tailWord_1752034, baseEnd_1752034] using wordTrace_append hprefix tailTrace_1752034
  have hstable : (prefixWord ++ tailWord_1752034).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752034).length < 2 ^ (prefixWord ++ tailWord_1752034).sum := by decide
  have hdescent : baseEnd_1752034 < baseStart_1752034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752093 : List Nat := [1, 4, 2, 2, 3, 9]
def baseStart_1752093 : Nat := 118140960795 + 1752093 * 2 ^ 59
def prefixEnd_1752093 : Nat := 4983230072969 + 3 ^ 40 * 1752093 * 2
def baseEnd_1752093 : Nat := 14809314574125410070449

theorem tailTrace_1752093 : CollatzResearch.WordTrace tailWord_1752093 prefixEnd_1752093 14809314574125410070449 := by
  unfold tailWord_1752093
  simp only [CollatzResearch.WordTrace]
  refine ⟨63904081641473769506300933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42602721094315846337533955 63904081641473769506300933)
  ·
    refine ⟨11982015307776331782431425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63904081641473769506300933 11982015307776331782431425)
    ·
      refine ⟨8986511480832248836823569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11982015307776331782431425 8986511480832248836823569)
      ·
        refine ⟨6739883610624186627617677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8986511480832248836823569 6739883610624186627617677)
        ·
          refine ⟨2527456353984069985356629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6739883610624186627617677 2527456353984069985356629)
          ·
            refine ⟨14809314574125410070449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2527456353984069985356629 14809314574125410070449)
            ·
              rfl

theorem cell21_1752093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 9].length) (baseStart_1752093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1752093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1752093 prefixEnd_1752093 := by exact prefixLift 1752093
  have htrace : WordTrace (prefixWord ++ tailWord_1752093) baseStart_1752093 baseEnd_1752093 := by
    simpa [prefixWord, tailWord_1752093, baseEnd_1752093] using wordTrace_append hprefix tailTrace_1752093
  have hstable : (prefixWord ++ tailWord_1752093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752093).length < 2 ^ (prefixWord ++ tailWord_1752093).sum := by decide
  have hdescent : baseEnd_1752093 < baseStart_1752093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752107 : List Nat := [1, 1, 1, 1, 2, 1, 6, 3, 5]
def baseStart_1752107 : Nat := 118140960795 + 1752107 * 2 ^ 59
def prefixEnd_1752107 : Nat := 4983230072969 + 3 ^ 40 * 1752107 * 2
def baseEnd_1752107 : Nat := 399854688492125158668761

theorem tailTrace_1752107 : CollatzResearch.WordTrace tailWord_1752107 prefixEnd_1752107 399854688492125158668761 := by
  unfold tailWord_1752107
  simp only [CollatzResearch.WordTrace]
  refine ⟨63904592263423049897310575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42603061508948699931540383 63904592263423049897310575)
  ·
    refine ⟨95856888395134574845965863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63904592263423049897310575 95856888395134574845965863)
    ·
      refine ⟨143785332592701862268948795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95856888395134574845965863 143785332592701862268948795)
      ·
        refine ⟨215677998889052793403423193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143785332592701862268948795 215677998889052793403423193)
        ·
          refine ⟨161758499166789595052567395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215677998889052793403423193 161758499166789595052567395)
          ·
            refine ⟨242637748750184392578851093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161758499166789595052567395 242637748750184392578851093)
            ·
              refine ⟨11373644472664893402133645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 242637748750184392578851093 11373644472664893402133645)
              ·
                refine ⟨4265116677249335025800117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11373644472664893402133645 4265116677249335025800117)
                ·
                  refine ⟨399854688492125158668761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4265116677249335025800117 399854688492125158668761)
                  ·
                    rfl

theorem cell21_1752107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 5].length) (baseStart_1752107 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1752107 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1752107 prefixEnd_1752107 := by exact prefixLift 1752107
  have htrace : WordTrace (prefixWord ++ tailWord_1752107) baseStart_1752107 baseEnd_1752107 := by
    simpa [prefixWord, tailWord_1752107, baseEnd_1752107] using wordTrace_append hprefix tailTrace_1752107
  have hstable : (prefixWord ++ tailWord_1752107).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752107).length < 2 ^ (prefixWord ++ tailWord_1752107).sum := by decide
  have hdescent : baseEnd_1752107 < baseStart_1752107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752124 : List Nat := [2, 2, 2, 2, 2, 3, 1, 2, 5]
def baseStart_1752124 : Nat := 118140960795 + 1752124 * 2 ^ 59
def prefixEnd_1752124 : Nat := 4983230072969 + 3 ^ 40 * 1752124 * 2
def baseEnd_1752124 : Nat := 399858568123736906885393

theorem tailTrace_1752124 : CollatzResearch.WordTrace tailWord_1752124 prefixEnd_1752124 399858568123736906885393 := by
  unfold tailWord_1752124
  simp only [CollatzResearch.WordTrace]
  refine ⟨31952606152180730900339713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42603474869574307867119617 31952606152180730900339713)
  ·
    refine ⟨23964454614135548175254785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31952606152180730900339713 23964454614135548175254785)
    ·
      refine ⟨17973340960601661131441089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23964454614135548175254785 17973340960601661131441089)
      ·
        refine ⟨13480005720451245848580817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17973340960601661131441089 13480005720451245848580817)
        ·
          refine ⟨10110004290338434386435613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13480005720451245848580817 10110004290338434386435613)
          ·
            refine ⟨3791251608876912894913355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10110004290338434386435613 3791251608876912894913355)
            ·
              refine ⟨5686877413315369342370033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3791251608876912894913355 5686877413315369342370033)
              ·
                refine ⟨4265158059986527006777525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5686877413315369342370033 4265158059986527006777525)
                ·
                  refine ⟨399858568123736906885393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4265158059986527006777525 399858568123736906885393)
                  ·
                    rfl

theorem cell21_1752124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 5].length) (baseStart_1752124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1752124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1752124 prefixEnd_1752124 := by exact prefixLift 1752124
  have htrace : WordTrace (prefixWord ++ tailWord_1752124) baseStart_1752124 baseEnd_1752124 := by
    simpa [prefixWord, tailWord_1752124, baseEnd_1752124] using wordTrace_append hprefix tailTrace_1752124
  have hstable : (prefixWord ++ tailWord_1752124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752124).length < 2 ^ (prefixWord ++ tailWord_1752124).sum := by decide
  have hdescent : baseEnd_1752124 < baseStart_1752124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752152 : List Nat := [2, 1, 2, 2, 1, 3, 10]
def baseStart_1752152 : Nat := 118140960795 + 1752152 * 2 ^ 59
def prefixEnd_1752152 : Nat := 4983230072969 + 3 ^ 40 * 1752152 * 2
def baseEnd_1752152 : Nat := 44429439789468342268741

theorem tailTrace_1752152 : CollatzResearch.WordTrace tailWord_1752152 prefixEnd_1752152 44429439789468342268741 := by
  unfold tailWord_1752152
  simp only [CollatzResearch.WordTrace]
  refine ⟨31953116774130011291349355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42604155698840015055132473 31953116774130011291349355)
  ·
    refine ⟨47929675161195016937024033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31953116774130011291349355 47929675161195016937024033)
    ·
      refine ⟨35947256370896262702768025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47929675161195016937024033 35947256370896262702768025)
      ·
        refine ⟨26960442278172197027076019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35947256370896262702768025 26960442278172197027076019)
        ·
          refine ⟨40440663417258295540614029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26960442278172197027076019 40440663417258295540614029)
          ·
            refine ⟨15165248781471860827730261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40440663417258295540614029 15165248781471860827730261)
            ·
              refine ⟨44429439789468342268741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15165248781471860827730261 44429439789468342268741)
              ·
                rfl

theorem cell21_1752152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 10].length) (baseStart_1752152 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1752152 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1752152 prefixEnd_1752152 := by exact prefixLift 1752152
  have htrace : WordTrace (prefixWord ++ tailWord_1752152) baseStart_1752152 baseEnd_1752152 := by
    simpa [prefixWord, tailWord_1752152, baseEnd_1752152] using wordTrace_append hprefix tailTrace_1752152
  have hstable : (prefixWord ++ tailWord_1752152).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752152).length < 2 ^ (prefixWord ++ tailWord_1752152).sum := by decide
  have hdescent : baseEnd_1752152 < baseStart_1752152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752158 : List Nat := [4, 4, 1, 1, 1, 1, 1, 3, 5]
def baseStart_1752158 : Nat := 118140960795 + 1752158 * 2 ^ 59
def prefixEnd_1752158 : Nat := 4983230072969 + 3 ^ 40 * 1752158 * 2
def baseEnd_1752158 : Nat := 399866327386960403318657

theorem tailTrace_1752158 : CollatzResearch.WordTrace tailWord_1752158 prefixEnd_1752158 399866327386960403318657 := by
  unfold tailWord_1752158
  simp only [CollatzResearch.WordTrace]
  refine ⟨7988306548279785700927141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42604301590825523738278085 7988306548279785700927141)
  ·
    refine ⟨1497807477802459818923839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7988306548279785700927141 1497807477802459818923839)
    ·
      refine ⟨2246711216703689728385759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1497807477802459818923839 2246711216703689728385759)
      ·
        refine ⟨3370066825055534592578639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2246711216703689728385759 3370066825055534592578639)
        ·
          refine ⟨5055100237583301888867959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3370066825055534592578639 5055100237583301888867959)
          ·
            refine ⟨7582650356374952833301939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5055100237583301888867959 7582650356374952833301939)
            ·
              refine ⟨11373975534562429249952909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7582650356374952833301939 11373975534562429249952909)
              ·
                refine ⟨4265240825460910968732341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11373975534562429249952909 4265240825460910968732341)
                ·
                  refine ⟨399866327386960403318657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4265240825460910968732341 399866327386960403318657)
                  ·
                    rfl

theorem cell21_1752158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_1752158 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1752158 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1752158 prefixEnd_1752158 := by exact prefixLift 1752158
  have htrace : WordTrace (prefixWord ++ tailWord_1752158) baseStart_1752158 baseEnd_1752158 := by
    simpa [prefixWord, tailWord_1752158, baseEnd_1752158] using wordTrace_append hprefix tailTrace_1752158
  have hstable : (prefixWord ++ tailWord_1752158).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752158).length < 2 ^ (prefixWord ++ tailWord_1752158).sum := by decide
  have hdescent : baseEnd_1752158 < baseStart_1752158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752183 : List Nat := [1, 1, 3, 1, 1, 4, 1, 4, 5]
def baseStart_1752183 : Nat := 118140960795 + 1752183 * 2 ^ 59
def prefixEnd_1752183 : Nat := 4983230072969 + 3 ^ 40 * 1752183 * 2
def baseEnd_1752183 : Nat := 399872032727565915401939

theorem tailTrace_1752183 : CollatzResearch.WordTrace tailWord_1752183 prefixEnd_1752183 399872032727565915401939 := by
  unfold tailWord_1752183
  simp only [CollatzResearch.WordTrace]
  refine ⟨63907364211147714877077203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42604909474098476584718135 63907364211147714877077203)
  ·
    refine ⟨95861046316721572315615805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63907364211147714877077203 95861046316721572315615805)
    ·
      refine ⟨35947892368770589618355927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95861046316721572315615805 35947892368770589618355927)
      ·
        refine ⟨53921838553155884427533891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35947892368770589618355927 53921838553155884427533891)
        ·
          refine ⟨80882757829733826641300837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53921838553155884427533891 80882757829733826641300837)
          ·
            refine ⟨15165517093075092495243907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80882757829733826641300837 15165517093075092495243907)
            ·
              refine ⟨22748275639612638742865861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15165517093075092495243907 22748275639612638742865861)
              ·
                refine ⟨4265301682427369764287349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22748275639612638742865861 4265301682427369764287349)
                ·
                  refine ⟨399872032727565915401939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4265301682427369764287349 399872032727565915401939)
                  ·
                    rfl

theorem cell21_1752183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 5].length) (baseStart_1752183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1752183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1752183 prefixEnd_1752183 := by exact prefixLift 1752183
  have htrace : WordTrace (prefixWord ++ tailWord_1752183) baseStart_1752183 baseEnd_1752183 := by
    simpa [prefixWord, tailWord_1752183, baseEnd_1752183] using wordTrace_append hprefix tailTrace_1752183
  have hstable : (prefixWord ++ tailWord_1752183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752183).length < 2 ^ (prefixWord ++ tailWord_1752183).sum := by decide
  have hdescent : baseEnd_1752183 < baseStart_1752183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752324 : List Nat := [2, 3, 2, 2, 2, 3, 1, 2, 4]
def baseStart_1752324 : Nat := 118140960795 + 1752324 * 2 ^ 59
def prefixEnd_1752324 : Nat := 4983230072969 + 3 ^ 40 * 1752324 * 2
def baseEnd_1752324 : Nat := 399904210848581003551651

theorem tailTrace_1752324 : CollatzResearch.WordTrace tailWord_1752324 prefixEnd_1752324 399904210848581003551651 := by
  unfold tailWord_1752324
  simp only [CollatzResearch.WordTrace]
  refine ⟨31956253451818447978980013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42608337935757930638640017 31956253451818447978980013)
  ·
    refine ⟨11983595044431917992117505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31956253451818447978980013 11983595044431917992117505)
    ·
      refine ⟨8987696283323938494088129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11983595044431917992117505 8987696283323938494088129)
      ·
        refine ⟨6740772212492953870566097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8987696283323938494088129 6740772212492953870566097)
        ·
          refine ⟨5055579159369715402924573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6740772212492953870566097 5055579159369715402924573)
          ·
            refine ⟨1895842184763643276096715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5055579159369715402924573 1895842184763643276096715)
            ·
              refine ⟨2843763277145464914145073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1895842184763643276096715 2843763277145464914145073)
              ·
                refine ⟨2132822457859098685608805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2843763277145464914145073 2132822457859098685608805)
                ·
                  refine ⟨399904210848581003551651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2132822457859098685608805 399904210848581003551651)
                  ·
                    rfl

theorem cell21_1752324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_1752324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1752324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1752324 prefixEnd_1752324 := by exact prefixLift 1752324
  have htrace : WordTrace (prefixWord ++ tailWord_1752324) baseStart_1752324 baseEnd_1752324 := by
    simpa [prefixWord, tailWord_1752324, baseEnd_1752324] using wordTrace_append hprefix tailTrace_1752324
  have hstable : (prefixWord ++ tailWord_1752324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752324).length < 2 ^ (prefixWord ++ tailWord_1752324).sum := by decide
  have hdescent : baseEnd_1752324 < baseStart_1752324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752369 : List Nat := [1, 2, 2, 3, 3, 1, 3, 3, 3]
def baseStart_1752369 : Nat := 118140960795 + 1752369 * 2 ^ 59
def prefixEnd_1752369 : Nat := 4983230072969 + 3 ^ 40 * 1752369 * 2
def baseEnd_1752369 : Nat := 399914480461670925301559

theorem tailTrace_1752369 : CollatzResearch.WordTrace tailWord_1752369 prefixEnd_1752369 399914480461670925301559 := by
  unfold tailWord_1752369
  simp only [CollatzResearch.WordTrace]
  refine ⟨63914148188473868643348161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42609432125649245762232107 63914148188473868643348161)
  ·
    refine ⟨47935611141355401482511121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63914148188473868643348161 47935611141355401482511121)
    ·
      refine ⟨35951708356016551111883341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47935611141355401482511121 35951708356016551111883341)
      ·
        refine ⟨13481890633506206666956253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35951708356016551111883341 13481890633506206666956253)
        ·
          refine ⟨5055708987564827500108595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13481890633506206666956253 5055708987564827500108595)
          ·
            refine ⟨7583563481347241250162893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5055708987564827500108595 7583563481347241250162893)
            ·
              refine ⟨2843836305505215468811085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7583563481347241250162893 2843836305505215468811085)
              ·
                refine ⟨1066438614564455800804157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2843836305505215468811085 1066438614564455800804157)
                ·
                  refine ⟨399914480461670925301559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1066438614564455800804157 399914480461670925301559)
                  ·
                    rfl

theorem cell21_1752369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 3, 3].length) (baseStart_1752369 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1752369 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1752369 prefixEnd_1752369 := by exact prefixLift 1752369
  have htrace : WordTrace (prefixWord ++ tailWord_1752369) baseStart_1752369 baseEnd_1752369 := by
    simpa [prefixWord, tailWord_1752369, baseEnd_1752369] using wordTrace_append hprefix tailTrace_1752369
  have hstable : (prefixWord ++ tailWord_1752369).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752369).length < 2 ^ (prefixWord ++ tailWord_1752369).sum := by decide
  have hdescent : baseEnd_1752369 < baseStart_1752369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752380 : List Nat := [2, 2, 2, 2, 1, 3, 9]
def baseStart_1752380 : Nat := 118140960795 + 1752380 * 2 ^ 59
def prefixEnd_1752380 : Nat := 4983230072969 + 3 ^ 40 * 1752380 * 2
def baseEnd_1752380 : Nat := 44435221201281927846467

theorem tailTrace_1752380 : CollatzResearch.WordTrace tailWord_1752380 prefixEnd_1752380 44435221201281927846467 := by
  unfold tailWord_1752380
  simp only [CollatzResearch.WordTrace]
  refine ⟨31957274695717008760999297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42609699594289345014665729 31957274695717008760999297)
  ·
    refine ⟨23967956021787756570749473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31957274695717008760999297 23967956021787756570749473)
    ·
      refine ⟨17975967016340817428062105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23967956021787756570749473 17975967016340817428062105)
      ·
        refine ⟨13481975262255613071046579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17975967016340817428062105 13481975262255613071046579)
        ·
          refine ⟨20222962893383419606569869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13481975262255613071046579 20222962893383419606569869)
          ·
            refine ⟨7583611085018782352463701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20222962893383419606569869 7583611085018782352463701)
            ·
              refine ⟨44435221201281927846467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7583611085018782352463701 44435221201281927846467)
              ·
                rfl

theorem cell21_1752380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 9].length) (baseStart_1752380 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1752380 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1752380 prefixEnd_1752380 := by exact prefixLift 1752380
  have htrace : WordTrace (prefixWord ++ tailWord_1752380) baseStart_1752380 baseEnd_1752380 := by
    simpa [prefixWord, tailWord_1752380, baseEnd_1752380] using wordTrace_append hprefix tailTrace_1752380
  have hstable : (prefixWord ++ tailWord_1752380).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752380).length < 2 ^ (prefixWord ++ tailWord_1752380).sum := by decide
  have hdescent : baseEnd_1752380 < baseStart_1752380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752425 : List Nat := [1, 2, 1, 1, 1, 3, 2, 4, 6]
def baseStart_1752425 : Nat := 118140960795 + 1752425 * 2 ^ 59
def prefixEnd_1752425 : Nat := 4983230072969 + 3 ^ 40 * 1752425 * 2
def baseEnd_1752425 : Nat := 399927260424627272368111

theorem tailTrace_1752425 : CollatzResearch.WordTrace tailWord_1752425 prefixEnd_1752425 399927260424627272368111 := by
  unfold tailWord_1752425
  simp only [CollatzResearch.WordTrace]
  refine ⟨63916190676270990207386729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42610793784180660138257819 63916190676270990207386729)
  ·
    refine ⟨47937143007203242655540047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63916190676270990207386729 47937143007203242655540047)
    ·
      refine ⟨71905714510804863983310071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47937143007203242655540047 71905714510804863983310071)
      ·
        refine ⟨107858571766207295974965107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71905714510804863983310071 107858571766207295974965107)
        ·
          refine ⟨161787857649310943962447661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107858571766207295974965107 161787857649310943962447661)
          ·
            refine ⟨60670446618491603985917873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161787857649310943962447661 60670446618491603985917873)
            ·
              refine ⟨45502834963868702989438405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60670446618491603985917873 45502834963868702989438405)
              ·
                refine ⟨8531781555725381810519701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45502834963868702989438405 8531781555725381810519701)
                ·
                  refine ⟨399927260424627272368111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8531781555725381810519701 399927260424627272368111)
                  ·
                    rfl

theorem cell21_1752425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 6].length) (baseStart_1752425 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1752425 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1752425 prefixEnd_1752425 := by exact prefixLift 1752425
  have htrace : WordTrace (prefixWord ++ tailWord_1752425) baseStart_1752425 baseEnd_1752425 := by
    simpa [prefixWord, tailWord_1752425, baseEnd_1752425] using wordTrace_append hprefix tailTrace_1752425
  have hstable : (prefixWord ++ tailWord_1752425).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752425).length < 2 ^ (prefixWord ++ tailWord_1752425).sum := by decide
  have hdescent : baseEnd_1752425 < baseStart_1752425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752473 : List Nat := [1, 2, 1, 2, 1, 6, 3, 5]
def baseStart_1752473 : Nat := 118140960795 + 1752473 * 2 ^ 59
def prefixEnd_1752473 : Nat := 4983230072969 + 3 ^ 40 * 1752473 * 2
def baseEnd_1752473 : Nat := 133312738226196618522671

theorem tailTrace_1752473 : CollatzResearch.WordTrace tailWord_1752473 prefixEnd_1752473 133312738226196618522671 := by
  unfold tailWord_1752473
  simp only [CollatzResearch.WordTrace]
  refine ⟨63917941380097094405134073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42611960920064729603422715 63917941380097094405134073)
  ·
    refine ⟨47938456035072820803850555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63917941380097094405134073 47938456035072820803850555)
    ·
      refine ⟨71907684052609231205775833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47938456035072820803850555 71907684052609231205775833)
      ·
        refine ⟨53930763039456923404331875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71907684052609231205775833 53930763039456923404331875)
        ·
          refine ⟨80896144559185385106497813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53930763039456923404331875 80896144559185385106497813)
          ·
            refine ⟨3792006776211814926867085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 80896144559185385106497813 3792006776211814926867085)
            ·
              refine ⟨1422002541079430597575157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3792006776211814926867085 1422002541079430597575157)
              ·
                refine ⟨133312738226196618522671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1422002541079430597575157 133312738226196618522671)
                ·
                  rfl

theorem cell21_1752473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 5].length) (baseStart_1752473 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1752473 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1752473 prefixEnd_1752473 := by exact prefixLift 1752473
  have htrace : WordTrace (prefixWord ++ tailWord_1752473) baseStart_1752473 baseEnd_1752473 := by
    simpa [prefixWord, tailWord_1752473, baseEnd_1752473] using wordTrace_append hprefix tailTrace_1752473
  have hstable : (prefixWord ++ tailWord_1752473).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752473).length < 2 ^ (prefixWord ++ tailWord_1752473).sum := by decide
  have hdescent : baseEnd_1752473 < baseStart_1752473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752487 : List Nat := [1, 1, 6, 1, 1, 1, 1, 2, 7]
def baseStart_1752487 : Nat := 118140960795 + 1752487 * 2 ^ 59
def prefixEnd_1752487 : Nat := 4983230072969 + 3 ^ 40 * 1752487 * 2
def baseEnd_1752487 : Nat := 399941409669328942334651

theorem tailTrace_1752487 : CollatzResearch.WordTrace tailWord_1752487 prefixEnd_1752487 399941409669328942334651 := by
  unfold tailWord_1752487
  simp only [CollatzResearch.WordTrace]
  refine ⟨63918452002046374796143715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42612301334697583197429143 63918452002046374796143715)
  ·
    refine ⟨95877678003069562194215573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63918452002046374796143715 95877678003069562194215573)
    ·
      refine ⟨4494266156393885727853855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 95877678003069562194215573 4494266156393885727853855)
      ·
        refine ⟨6741399234590828591780783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4494266156393885727853855 6741399234590828591780783)
        ·
          refine ⟨10112098851886242887671175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6741399234590828591780783 10112098851886242887671175)
          ·
            refine ⟨15168148277829364331506763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10112098851886242887671175 15168148277829364331506763)
            ·
              refine ⟨22752222416744046497260145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15168148277829364331506763 22752222416744046497260145)
              ·
                refine ⟨17064166812558034872945109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22752222416744046497260145 17064166812558034872945109)
                ·
                  refine ⟨399941409669328942334651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17064166812558034872945109 399941409669328942334651)
                  ·
                    rfl

theorem cell21_1752487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 7].length) (baseStart_1752487 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1752487 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1752487 prefixEnd_1752487 := by exact prefixLift 1752487
  have htrace : WordTrace (prefixWord ++ tailWord_1752487) baseStart_1752487 baseEnd_1752487 := by
    simpa [prefixWord, tailWord_1752487, baseEnd_1752487] using wordTrace_append hprefix tailTrace_1752487
  have hstable : (prefixWord ++ tailWord_1752487).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752487).length < 2 ^ (prefixWord ++ tailWord_1752487).sum := by decide
  have hdescent : baseEnd_1752487 < baseStart_1752487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752504 : List Nat := [2, 1, 2, 1, 2, 2, 4, 4, 3]
def baseStart_1752504 : Nat := 118140960795 + 1752504 * 2 ^ 59
def prefixEnd_1752504 : Nat := 4983230072969 + 3 ^ 40 * 1752504 * 2
def baseEnd_1752504 : Nat := 399945289300940690551283

theorem tailTrace_1752504 : CollatzResearch.WordTrace tailWord_1752504 prefixEnd_1752504 399945289300940690551283 := by
  unfold tailWord_1752504
  simp only [CollatzResearch.WordTrace]
  refine ⟨31959536021492393349756283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42612714695323191133008377 31959536021492393349756283)
  ·
    refine ⟨47939304032238590024634425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31959536021492393349756283 47939304032238590024634425)
    ·
      refine ⟨35954478024178942518475819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47939304032238590024634425 35954478024178942518475819)
      ·
        refine ⟨53931717036268413777713729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35954478024178942518475819 53931717036268413777713729)
        ·
          refine ⟨40448787777201310333285297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53931717036268413777713729 40448787777201310333285297)
          ·
            refine ⟨30336590832900982749963973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40448787777201310333285297 30336590832900982749963973)
            ·
              refine ⟨5688110781168934265618245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30336590832900982749963973 5688110781168934265618245)
              ·
                refine ⟨1066520771469175174803421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5688110781168934265618245 1066520771469175174803421)
                ·
                  refine ⟨399945289300940690551283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1066520771469175174803421 399945289300940690551283)
                  ·
                    rfl

theorem cell21_1752504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 4, 3].length) (baseStart_1752504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1752504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1752504 prefixEnd_1752504 := by exact prefixLift 1752504
  have htrace : WordTrace (prefixWord ++ tailWord_1752504) baseStart_1752504 baseEnd_1752504 := by
    simpa [prefixWord, tailWord_1752504, baseEnd_1752504] using wordTrace_append hprefix tailTrace_1752504
  have hstable : (prefixWord ++ tailWord_1752504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752504).length < 2 ^ (prefixWord ++ tailWord_1752504).sum := by decide
  have hdescent : baseEnd_1752504 < baseStart_1752504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752549 : List Nat := [1, 3, 1, 5, 1, 3, 7]
def baseStart_1752549 : Nat := 118140960795 + 1752549 * 2 ^ 59
def prefixEnd_1752549 : Nat := 4983230072969 + 3 ^ 40 * 1752549 * 2
def baseEnd_1752549 : Nat := 44439506546003401366799

theorem tailTrace_1752549 : CollatzResearch.WordTrace tailWord_1752549 prefixEnd_1752549 44439506546003401366799 := by
  unfold tailWord_1752549
  simp only [CollatzResearch.WordTrace]
  refine ⟨63920713327821759384900701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42613808885214506256600467 63920713327821759384900701)
  ·
    refine ⟨23970267497933159769337763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63920713327821759384900701 23970267497933159769337763)
    ·
      refine ⟨35955401246899739654006645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23970267497933159769337763 35955401246899739654006645)
      ·
        refine ⟨3370818866896850592563123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35955401246899739654006645 3370818866896850592563123)
        ·
          refine ⟨5056228300345275888844685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3370818866896850592563123 5056228300345275888844685)
          ·
            refine ⟨1896085612629478458316757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5056228300345275888844685 1896085612629478458316757)
            ·
              refine ⟨44439506546003401366799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1896085612629478458316757 44439506546003401366799)
              ·
                rfl

theorem cell21_1752549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 7].length) (baseStart_1752549 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1752549 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1752549 prefixEnd_1752549 := by exact prefixLift 1752549
  have htrace : WordTrace (prefixWord ++ tailWord_1752549) baseStart_1752549 baseEnd_1752549 := by
    simpa [prefixWord, tailWord_1752549, baseEnd_1752549] using wordTrace_append hprefix tailTrace_1752549
  have hstable : (prefixWord ++ tailWord_1752549).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752549).length < 2 ^ (prefixWord ++ tailWord_1752549).sum := by decide
  have hdescent : baseEnd_1752549 < baseStart_1752549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752606 : List Nat := [4, 3, 3, 1, 2, 1, 2, 2, 3]
def baseStart_1752606 : Nat := 118140960795 + 1752606 * 2 ^ 59
def prefixEnd_1752606 : Nat := 4983230072969 + 3 ^ 40 * 1752606 * 2
def baseEnd_1752606 : Nat := 399968567090611179851075

theorem tailTrace_1752606 : CollatzResearch.WordTrace tailWord_1752606 prefixEnd_1752606 399968567090611179851075 := by
  unfold tailWord_1752606
  simp only [CollatzResearch.WordTrace]
  refine ⟨7990349036076907264965709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42615194859076838746483781 7990349036076907264965709)
  ·
    refine ⟨2996380888528840224362141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7990349036076907264965709 2996380888528840224362141)
    ·
      refine ⟨1123642833198315084135803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2996380888528840224362141 1123642833198315084135803)
      ·
        refine ⟨1685464249797472626203705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1123642833198315084135803 1685464249797472626203705)
        ·
          refine ⟨1264098187348104469652779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1685464249797472626203705 1264098187348104469652779)
          ·
            refine ⟨1896147281022156704479169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1264098187348104469652779 1896147281022156704479169)
            ·
              refine ⟨1422110460766617528359377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1896147281022156704479169 1422110460766617528359377)
              ·
                refine ⟨1066582845574963146269533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1422110460766617528359377 1066582845574963146269533)
                ·
                  refine ⟨399968567090611179851075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1066582845574963146269533 399968567090611179851075)
                  ·
                    rfl

theorem cell21_1752606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_1752606 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1752606 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1752606 prefixEnd_1752606 := by exact prefixLift 1752606
  have htrace : WordTrace (prefixWord ++ tailWord_1752606) baseStart_1752606 baseEnd_1752606 := by
    simpa [prefixWord, tailWord_1752606, baseEnd_1752606] using wordTrace_append hprefix tailTrace_1752606
  have hstable : (prefixWord ++ tailWord_1752606).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752606).length < 2 ^ (prefixWord ++ tailWord_1752606).sum := by decide
  have hdescent : baseEnd_1752606 < baseStart_1752606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752608 : List Nat := [2, 1, 1, 6, 1, 10]
def baseStart_1752608 : Nat := 118140960795 + 1752608 * 2 ^ 59
def prefixEnd_1752608 : Nat := 4983230072969 + 3 ^ 40 * 1752608 * 2
def baseEnd_1752608 : Nat := 14813667537698504474731

theorem tailTrace_1752608 : CollatzResearch.WordTrace tailWord_1752608 prefixEnd_1752608 14813667537698504474731 := by
  unfold tailWord_1752608
  simp only [CollatzResearch.WordTrace]
  refine ⟨31961432617304006230649239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42615243489738674974198985 31961432617304006230649239)
  ·
    refine ⟨47942148925956009345973859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31961432617304006230649239 47942148925956009345973859)
    ·
      refine ⟨71913223388934014018960789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47942148925956009345973859 71913223388934014018960789)
      ·
        refine ⟨3370932346356281907138787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 71913223388934014018960789 3370932346356281907138787)
        ·
          refine ⟨5056398519534422860708181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3370932346356281907138787 5056398519534422860708181)
          ·
            refine ⟨14813667537698504474731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5056398519534422860708181 14813667537698504474731)
            ·
              rfl

theorem cell21_1752608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 10].length) (baseStart_1752608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1752608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1752608 prefixEnd_1752608 := by exact prefixLift 1752608
  have htrace : WordTrace (prefixWord ++ tailWord_1752608) baseStart_1752608 baseEnd_1752608 := by
    simpa [prefixWord, tailWord_1752608, baseEnd_1752608] using wordTrace_append hprefix tailTrace_1752608
  have hstable : (prefixWord ++ tailWord_1752608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752608).length < 2 ^ (prefixWord ++ tailWord_1752608).sum := by decide
  have hdescent : baseEnd_1752608 < baseStart_1752608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752611 : List Nat := [1, 1, 1, 4, 5, 1, 2, 2, 4]
def baseStart_1752611 : Nat := 118140960795 + 1752611 * 2 ^ 59
def prefixEnd_1752611 : Nat := 4983230072969 + 3 ^ 40 * 1752611 * 2
def baseEnd_1752611 : Nat := 399969708158732282267731

theorem tailTrace_1752611 : CollatzResearch.WordTrace tailWord_1752611 prefixEnd_1752611 399969708158732282267731 := by
  unfold tailWord_1752611
  simp only [CollatzResearch.WordTrace]
  refine ⟨63922974653597143973657687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42615316435731429315771791 63922974653597143973657687)
  ·
    refine ⟨95884461980395715960486531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63922974653597143973657687 95884461980395715960486531)
    ·
      refine ⟨143826692970593573940729797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95884461980395715960486531 143826692970593573940729797)
      ·
        refine ⟨26967504931986295113886837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143826692970593573940729797 26967504931986295113886837)
        ·
          refine ⟨2528203587373715166926891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26967504931986295113886837 2528203587373715166926891)
          ·
            refine ⟨3792305381060572750390337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2528203587373715166926891 3792305381060572750390337)
            ·
              refine ⟨2844229035795429562792753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3792305381060572750390337 2844229035795429562792753)
              ·
                refine ⟨2133171776846572172094565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2844229035795429562792753 2133171776846572172094565)
                ·
                  refine ⟨399969708158732282267731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2133171776846572172094565 399969708158732282267731)
                  ·
                    rfl

theorem cell21_1752611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 2, 4].length) (baseStart_1752611 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1752611 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1752611 prefixEnd_1752611 := by exact prefixLift 1752611
  have htrace : WordTrace (prefixWord ++ tailWord_1752611) baseStart_1752611 baseEnd_1752611 := by
    simpa [prefixWord, tailWord_1752611, baseEnd_1752611] using wordTrace_append hprefix tailTrace_1752611
  have hstable : (prefixWord ++ tailWord_1752611).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752611).length < 2 ^ (prefixWord ++ tailWord_1752611).sum := by decide
  have hdescent : baseEnd_1752611 < baseStart_1752611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752639 : List Nat := [1, 1, 2, 2, 3, 4, 1, 2, 5]
def baseStart_1752639 : Nat := 118140960795 + 1752639 * 2 ^ 59
def prefixEnd_1752639 : Nat := 4983230072969 + 3 ^ 40 * 1752639 * 2
def baseEnd_1752639 : Nat := 399976098140210455801007

theorem tailTrace_1752639 : CollatzResearch.WordTrace tailWord_1752639 prefixEnd_1752639 399976098140210455801007 := by
  unfold tailWord_1752639
  simp only [CollatzResearch.WordTrace]
  refine ⟨63923995897495704755676971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42615997264997136503784647 63923995897495704755676971)
  ·
    refine ⟨95885993846243557133515457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63923995897495704755676971 95885993846243557133515457)
    ·
      refine ⟨71914495384682667850136593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95885993846243557133515457 71914495384682667850136593)
      ·
        refine ⟨53935871538512000887602445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71914495384682667850136593 53935871538512000887602445)
        ·
          refine ⟨20225951826942000332850917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53935871538512000887602445 20225951826942000332850917)
          ·
            refine ⟨3792365967551625062409547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20225951826942000332850917 3792365967551625062409547)
            ·
              refine ⟨5688548951327437593614321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3792365967551625062409547 5688548951327437593614321)
              ·
                refine ⟨4266411713495578195210741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5688548951327437593614321 4266411713495578195210741)
                ·
                  refine ⟨399976098140210455801007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4266411713495578195210741 399976098140210455801007)
                  ·
                    rfl

theorem cell21_1752639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 5].length) (baseStart_1752639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1752639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1752639 prefixEnd_1752639 := by exact prefixLift 1752639
  have htrace : WordTrace (prefixWord ++ tailWord_1752639) baseStart_1752639 baseEnd_1752639 := by
    simpa [prefixWord, tailWord_1752639, baseEnd_1752639] using wordTrace_append hprefix tailTrace_1752639
  have hstable : (prefixWord ++ tailWord_1752639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752639).length < 2 ^ (prefixWord ++ tailWord_1752639).sum := by decide
  have hdescent : baseEnd_1752639 < baseStart_1752639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752656 : List Nat := [2, 1, 1, 1, 1, 3, 6, 3, 3]
def baseStart_1752656 : Nat := 118140960795 + 1752656 * 2 ^ 59
def prefixEnd_1752656 : Nat := 4983230072969 + 3 ^ 40 * 1752656 * 2
def baseEnd_1752656 : Nat := 399979977771822204017639

theorem tailTrace_1752656 : CollatzResearch.WordTrace tailWord_1752656 prefixEnd_1752656 399979977771822204017639 := by
  unfold tailWord_1752656
  simp only [CollatzResearch.WordTrace]
  refine ⟨31962307969217058329522911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42616410625622744439363881 31962307969217058329522911)
  ·
    refine ⟨47943461953825587494284367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31962307969217058329522911 47943461953825587494284367)
    ·
      refine ⟨71915192930738381241426551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47943461953825587494284367 71915192930738381241426551)
      ·
        refine ⟨107872789396107571862139827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71915192930738381241426551 107872789396107571862139827)
        ·
          refine ⟨161809184094161357793209741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107872789396107571862139827 161809184094161357793209741)
          ·
            refine ⟨60678444035310509172453653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161809184094161357793209741 60678444035310509172453653)
            ·
              refine ⟨2844302064155180117458765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 60678444035310509172453653 2844302064155180117458765)
              ·
                refine ⟨1066613274058192544047037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2844302064155180117458765 1066613274058192544047037)
                ·
                  refine ⟨399979977771822204017639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1066613274058192544047037 399979977771822204017639)
                  ·
                    rfl

theorem cell21_1752656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 3, 3].length) (baseStart_1752656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1752656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1752656 prefixEnd_1752656 := by exact prefixLift 1752656
  have htrace : WordTrace (prefixWord ++ tailWord_1752656) baseStart_1752656 baseEnd_1752656 := by
    simpa [prefixWord, tailWord_1752656, baseEnd_1752656] using wordTrace_append hprefix tailTrace_1752656
  have hstable : (prefixWord ++ tailWord_1752656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752656).length < 2 ^ (prefixWord ++ tailWord_1752656).sum := by decide
  have hdescent : baseEnd_1752656 < baseStart_1752656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752662 : List Nat := [5, 2, 2, 2, 1, 2, 1, 2, 4]
def baseStart_1752662 : Nat := 118140960795 + 1752662 * 2 ^ 59
def prefixEnd_1752662 : Nat := 4983230072969 + 3 ^ 40 * 1752662 * 2
def baseEnd_1752662 : Nat := 399981347053567526917627

theorem tailTrace_1752662 : CollatzResearch.WordTrace tailWord_1752662 prefixEnd_1752662 399981347053567526917627 := by
  unfold tailWord_1752662
  simp only [CollatzResearch.WordTrace]
  refine ⟨3995302173525773730235265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42616556517608253122509493 3995302173525773730235265)
  ·
    refine ⟨2996476630144330297676449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3995302173525773730235265 2996476630144330297676449)
    ·
      refine ⟨2247357472608247723257337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2996476630144330297676449 2247357472608247723257337)
      ·
        refine ⟨1685518104456185792443003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2247357472608247723257337 1685518104456185792443003)
        ·
          refine ⟨2528277156684278688664505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1685518104456185792443003 2528277156684278688664505)
          ·
            refine ⟨1896207867513209016498379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2528277156684278688664505 1896207867513209016498379)
            ·
              refine ⟨2844311801269813524747569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1896207867513209016498379 2844311801269813524747569)
              ·
                refine ⟨2133233850952360143560677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2844311801269813524747569 2133233850952360143560677)
                ·
                  refine ⟨399981347053567526917627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2133233850952360143560677 399981347053567526917627)
                  ·
                    rfl

theorem cell21_1752662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_1752662 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1752662 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1752662 prefixEnd_1752662 := by exact prefixLift 1752662
  have htrace : WordTrace (prefixWord ++ tailWord_1752662) baseStart_1752662 baseEnd_1752662 := by
    simpa [prefixWord, tailWord_1752662, baseEnd_1752662] using wordTrace_append hprefix tailTrace_1752662
  have hstable : (prefixWord ++ tailWord_1752662).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752662).length < 2 ^ (prefixWord ++ tailWord_1752662).sum := by decide
  have hdescent : baseEnd_1752662 < baseStart_1752662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752698 : List Nat := [3, 1, 1, 1, 1, 1, 1, 5, 7]
def baseStart_1752698 : Nat := 118140960795 + 1752698 * 2 ^ 59
def prefixEnd_1752698 : Nat := 4983230072969 + 3 ^ 40 * 1752698 * 2
def baseEnd_1752698 : Nat := 399989562744039464317553

theorem tailTrace_1752698 : CollatzResearch.WordTrace tailWord_1752698 prefixEnd_1752698 399989562744039464317553 := by
  unfold tailWord_1752698
  simp only [CollatzResearch.WordTrace]
  refine ⟨15981536951070489458018687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42617431869521305221383165 15981536951070489458018687)
  ·
    refine ⟨23972305426605734187028031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15981536951070489458018687 23972305426605734187028031)
    ·
      refine ⟨35958458139908601280542047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23972305426605734187028031 35958458139908601280542047)
      ·
        refine ⟨53937687209862901920813071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35958458139908601280542047 53937687209862901920813071)
        ·
          refine ⟨80906530814794352881219607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53937687209862901920813071 80906530814794352881219607)
          ·
            refine ⟨121359796222191529321829411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80906530814794352881219607 121359796222191529321829411)
            ·
              refine ⟨182039694333287293982744117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121359796222191529321829411 182039694333287293982744117)
              ·
                refine ⟨17066221343745683810882261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 182039694333287293982744117 17066221343745683810882261)
                ·
                  refine ⟨399989562744039464317553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17066221343745683810882261 399989562744039464317553)
                  ·
                    rfl

theorem cell21_1752698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 7].length) (baseStart_1752698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1752698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1752698 prefixEnd_1752698 := by exact prefixLift 1752698
  have htrace : WordTrace (prefixWord ++ tailWord_1752698) baseStart_1752698 baseEnd_1752698 := by
    simpa [prefixWord, tailWord_1752698, baseEnd_1752698] using wordTrace_append hprefix tailTrace_1752698
  have hstable : (prefixWord ++ tailWord_1752698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752698).length < 2 ^ (prefixWord ++ tailWord_1752698).sum := by decide
  have hdescent : baseEnd_1752698 < baseStart_1752698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752701 : List Nat := [1, 4, 1, 1, 4, 1, 4, 5]
def baseStart_1752701 : Nat := 118140960795 + 1752701 * 2 ^ 59
def prefixEnd_1752701 : Nat := 4983230072969 + 3 ^ 40 * 1752701 * 2
def baseEnd_1752701 : Nat := 133330082461637375255849

theorem tailTrace_1752701 : CollatzResearch.WordTrace tailWord_1752701 prefixEnd_1752701 133330082461637375255849 := by
  unfold tailWord_1752701
  simp only [CollatzResearch.WordTrace]
  refine ⟨63926257223271089344433957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42617504815514059562955971 63926257223271089344433957)
  ·
    refine ⟨11986173229363329252081367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63926257223271089344433957 11986173229363329252081367)
    ·
      refine ⟨17979259844044993878122051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11986173229363329252081367 17979259844044993878122051)
      ·
        refine ⟨26968889766067490817183077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17979259844044993878122051 26968889766067490817183077)
        ·
          refine ⟨5056666831137654528221827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26968889766067490817183077 5056666831137654528221827)
          ·
            refine ⟨7585000246706481792332741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5056666831137654528221827 7585000246706481792332741)
            ·
              refine ⟨1422187546257465336062389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7585000246706481792332741 1422187546257465336062389)
              ·
                refine ⟨133330082461637375255849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1422187546257465336062389 133330082461637375255849)
                ·
                  rfl

theorem cell21_1752701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 5].length) (baseStart_1752701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1752701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1752701 prefixEnd_1752701 := by exact prefixLift 1752701
  have htrace : WordTrace (prefixWord ++ tailWord_1752701) baseStart_1752701 baseEnd_1752701 := by
    simpa [prefixWord, tailWord_1752701, baseEnd_1752701] using wordTrace_append hprefix tailTrace_1752701
  have hstable : (prefixWord ++ tailWord_1752701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752701).length < 2 ^ (prefixWord ++ tailWord_1752701).sum := by decide
  have hdescent : baseEnd_1752701 < baseStart_1752701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752738 : List Nat := [3, 3, 1, 4, 2, 1, 2, 1, 4]
def baseStart_1752738 : Nat := 118140960795 + 1752738 * 2 ^ 59
def prefixEnd_1752738 : Nat := 4983230072969 + 3 ^ 40 * 1752738 * 2
def baseEnd_1752738 : Nat := 399998691289008283650805

theorem tailTrace_1752738 : CollatzResearch.WordTrace tailWord_1752738 prefixEnd_1752738 399998691289008283650805 := by
  unfold tailWord_1752738
  simp only [CollatzResearch.WordTrace]
  refine ⟨15981901681034261165882717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42618404482758029775687245 15981901681034261165882717)
  ·
    refine ⟨5993213130387847937206019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15981901681034261165882717 5993213130387847937206019)
    ·
      refine ⟨8989819695581771905809029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5993213130387847937206019 8989819695581771905809029)
      ·
        refine ⟨1685591192921582232339193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8989819695581771905809029 1685591192921582232339193)
        ·
          refine ⟨1264193394691186674254395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1685591192921582232339193 1264193394691186674254395)
          ·
            refine ⟨1896290092036780011381593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1264193394691186674254395 1896290092036780011381593)
            ·
              refine ⟨1422217569027585008536195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1896290092036780011381593 1422217569027585008536195)
              ·
                refine ⟨2133326353541377512804293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1422217569027585008536195 2133326353541377512804293)
                ·
                  refine ⟨399998691289008283650805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2133326353541377512804293 399998691289008283650805)
                  ·
                    rfl

theorem cell21_1752738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_1752738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1752738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1752738 prefixEnd_1752738 := by exact prefixLift 1752738
  have htrace : WordTrace (prefixWord ++ tailWord_1752738) baseStart_1752738 baseEnd_1752738 := by
    simpa [prefixWord, tailWord_1752738, baseEnd_1752738] using wordTrace_append hprefix tailTrace_1752738
  have hstable : (prefixWord ++ tailWord_1752738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752738).length < 2 ^ (prefixWord ++ tailWord_1752738).sum := by decide
  have hdescent : baseEnd_1752738 < baseStart_1752738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752819 : List Nat := [1, 1, 1, 2, 2, 3, 2, 9]
def baseStart_1752819 : Nat := 118140960795 + 1752819 * 2 ^ 59
def prefixEnd_1752819 : Nat := 4983230072969 + 3 ^ 40 * 1752819 * 2
def baseEnd_1752819 : Nat := 133339058864190047600213

theorem tailTrace_1752819 : CollatzResearch.WordTrace tailWord_1752819 prefixEnd_1752819 133339058864190047600213 := by
  unfold tailWord_1752819
  simp only [CollatzResearch.WordTrace]
  refine ⟨63930561036843595497229511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42620374024562396998153007 63930561036843595497229511)
  ·
    refine ⟨95895841555265393245844267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63930561036843595497229511 95895841555265393245844267)
    ·
      refine ⟨143843762332898089868766401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95895841555265393245844267 143843762332898089868766401)
      ·
        refine ⟨107882821749673567401574801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143843762332898089868766401 107882821749673567401574801)
        ·
          refine ⟨80912116312255175551181101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107882821749673567401574801 80912116312255175551181101)
          ·
            refine ⟨30342043617095690831692913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80912116312255175551181101 30342043617095690831692913)
            ·
              refine ⟨22756532712821768123769685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30342043617095690831692913 22756532712821768123769685)
              ·
                refine ⟨133339058864190047600213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22756532712821768123769685 133339058864190047600213)
                ·
                  rfl

theorem cell21_1752819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 9].length) (baseStart_1752819 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1752819 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1752819 prefixEnd_1752819 := by exact prefixLift 1752819
  have htrace : WordTrace (prefixWord ++ tailWord_1752819) baseStart_1752819 baseEnd_1752819 := by
    simpa [prefixWord, tailWord_1752819, baseEnd_1752819] using wordTrace_append hprefix tailTrace_1752819
  have hstable : (prefixWord ++ tailWord_1752819).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752819).length < 2 ^ (prefixWord ++ tailWord_1752819).sum := by decide
  have hdescent : baseEnd_1752819 < baseStart_1752819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752836 : List Nat := [2, 3, 2, 2, 1, 3, 8]
def baseStart_1752836 : Nat := 118140960795 + 1752836 * 2 ^ 59
def prefixEnd_1752836 : Nat := 4983230072969 + 3 ^ 40 * 1752836 * 2
def baseEnd_1752836 : Nat := 44446784024909099001919

theorem tailTrace_1752836 : CollatzResearch.WordTrace tailWord_1752836 prefixEnd_1752836 44446784024909099001919 := by
  unfold tailWord_1752836
  simp only [CollatzResearch.WordTrace]
  refine ⟨31965590538891003700299181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42620787385188004933732241 31965590538891003700299181)
  ·
    refine ⟨11987096452084126387612193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31965590538891003700299181 11987096452084126387612193)
    ·
      refine ⟨8990322339063094790709145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11987096452084126387612193 8990322339063094790709145)
      ·
        refine ⟨6742741754297321093031859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8990322339063094790709145 6742741754297321093031859)
        ·
          refine ⟨10114112631445981639547789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6742741754297321093031859 10114112631445981639547789)
          ·
            refine ⟨3792792236792243114830421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10114112631445981639547789 3792792236792243114830421)
            ·
              refine ⟨44446784024909099001919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3792792236792243114830421 44446784024909099001919)
              ·
                rfl

theorem cell21_1752836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 8].length) (baseStart_1752836 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1752836 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1752836 prefixEnd_1752836 := by exact prefixLift 1752836
  have htrace : WordTrace (prefixWord ++ tailWord_1752836) baseStart_1752836 baseEnd_1752836 := by
    simpa [prefixWord, tailWord_1752836, baseEnd_1752836] using wordTrace_append hprefix tailTrace_1752836
  have hstable : (prefixWord ++ tailWord_1752836).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752836).length < 2 ^ (prefixWord ++ tailWord_1752836).sum := by decide
  have hdescent : baseEnd_1752836 < baseStart_1752836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1752881 : List Nat := [1, 2, 2, 3, 2, 2, 1, 2, 6]
def baseStart_1752881 : Nat := 118140960795 + 1752881 * 2 ^ 59
def prefixEnd_1752881 : Nat := 4983230072969 + 3 ^ 40 * 1752881 * 2
def baseEnd_1752881 : Nat := 400031325837271812767179

theorem tailTrace_1752881 : CollatzResearch.WordTrace tailWord_1752881 prefixEnd_1752881 400031325837271812767179 := by
  unfold tailWord_1752881
  simp only [CollatzResearch.WordTrace]
  refine ⟨63932822362618980085986497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42621881575079320057324331 63932822362618980085986497)
  ·
    refine ⟨47949616771964235064489873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63932822362618980085986497 47949616771964235064489873)
    ·
      refine ⟨35962212578973176298367405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47949616771964235064489873 35962212578973176298367405)
      ·
        refine ⟨13485829717114941111887777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35962212578973176298367405 13485829717114941111887777)
        ·
          refine ⟨10114372287836205833915833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13485829717114941111887777 10114372287836205833915833)
          ·
            refine ⟨7585779215877154375436875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10114372287836205833915833 7585779215877154375436875)
            ·
              refine ⟨11378668823815731563155313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7585779215877154375436875 11378668823815731563155313)
              ·
                refine ⟨8534001617861798672366485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11378668823815731563155313 8534001617861798672366485)
                ·
                  refine ⟨400031325837271812767179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8534001617861798672366485 400031325837271812767179)
                  ·
                    rfl

theorem cell21_1752881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 6].length) (baseStart_1752881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1752881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1752881 prefixEnd_1752881 := by exact prefixLift 1752881
  have htrace : WordTrace (prefixWord ++ tailWord_1752881) baseStart_1752881 baseEnd_1752881 := by
    simpa [prefixWord, tailWord_1752881, baseEnd_1752881] using wordTrace_append hprefix tailTrace_1752881
  have hstable : (prefixWord ++ tailWord_1752881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1752881).length < 2 ^ (prefixWord ++ tailWord_1752881).sum := by decide
  have hdescent : baseEnd_1752881 < baseStart_1752881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1752881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753047 : List Nat := [1, 1, 3, 2, 1, 1, 5, 7]
def baseStart_1753047 : Nat := 118140960795 + 1753047 * 2 ^ 59
def prefixEnd_1753047 : Nat := 4983230072969 + 3 ^ 40 * 1753047 * 2
def baseEnd_1753047 : Nat := 133356403099630804333391

theorem tailTrace_1753047 : CollatzResearch.WordTrace tailWord_1753047 prefixEnd_1753047 133356403099630804333391 := by
  unfold tailWord_1753047
  simp only [CollatzResearch.WordTrace]
  refine ⟨63938876880017590436529395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42625917920011726957686263 63938876880017590436529395)
  ·
    refine ⟨95908315320026385654794093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63938876880017590436529395 95908315320026385654794093)
    ·
      refine ⟨35965618245009894620547785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95908315320026385654794093 35965618245009894620547785)
      ·
        refine ⟨26974213683757420965410839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35965618245009894620547785 26974213683757420965410839)
        ·
          refine ⟨40461320525636131448116259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26974213683757420965410839 40461320525636131448116259)
          ·
            refine ⟨60691980788454197172174389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40461320525636131448116259 60691980788454197172174389)
            ·
              refine ⟨5689873198917580984891349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60691980788454197172174389 5689873198917580984891349)
              ·
                refine ⟨133356403099630804333391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5689873198917580984891349 133356403099630804333391)
                ·
                  rfl

theorem cell21_1753047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 7].length) (baseStart_1753047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1753047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1753047 prefixEnd_1753047 := by exact prefixLift 1753047
  have htrace : WordTrace (prefixWord ++ tailWord_1753047) baseStart_1753047 baseEnd_1753047 := by
    simpa [prefixWord, tailWord_1753047, baseEnd_1753047] using wordTrace_append hprefix tailTrace_1753047
  have hstable : (prefixWord ++ tailWord_1753047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753047).length < 2 ^ (prefixWord ++ tailWord_1753047).sum := by decide
  have hdescent : baseEnd_1753047 < baseStart_1753047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753247 : List Nat := [1, 1, 2, 6, 1, 1, 3, 1, 5]
def baseStart_1753247 : Nat := 118140960795 + 1753247 * 2 ^ 59
def prefixEnd_1753247 : Nat := 4983230072969 + 3 ^ 40 * 1753247 * 2
def baseEnd_1753247 : Nat := 400114852023736509666431

theorem tailTrace_1753247 : CollatzResearch.WordTrace tailWord_1753247 prefixEnd_1753247 400114852023736509666431 := by
  unfold tailWord_1753247
  simp only [CollatzResearch.WordTrace]
  refine ⟨63946171479293024593809995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42630780986195349729206663 63946171479293024593809995)
  ·
    refine ⟨95919257218939536890714993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63946171479293024593809995 95919257218939536890714993)
    ·
      refine ⟨71939442914204652668036245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95919257218939536890714993 71939442914204652668036245)
      ·
        refine ⟨3372161386603343093814199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 71939442914204652668036245 3372161386603343093814199)
        ·
          refine ⟨5058242079905014640721299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3372161386603343093814199 5058242079905014640721299)
          ·
            refine ⟨7587363119857521961081949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5058242079905014640721299 7587363119857521961081949)
            ·
              refine ⟨2845261169946570735405731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7587363119857521961081949 2845261169946570735405731)
              ·
                refine ⟨4267891754919856103108597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2845261169946570735405731 4267891754919856103108597)
                ·
                  refine ⟨400114852023736509666431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4267891754919856103108597 400114852023736509666431)
                  ·
                    rfl

theorem cell21_1753247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 5].length) (baseStart_1753247 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1753247 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1753247 prefixEnd_1753247 := by exact prefixLift 1753247
  have htrace : WordTrace (prefixWord ++ tailWord_1753247) baseStart_1753247 baseEnd_1753247 := by
    simpa [prefixWord, tailWord_1753247, baseEnd_1753247] using wordTrace_append hprefix tailTrace_1753247
  have hstable : (prefixWord ++ tailWord_1753247).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753247).length < 2 ^ (prefixWord ++ tailWord_1753247).sum := by decide
  have hdescent : baseEnd_1753247 < baseStart_1753247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753289 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 9]
def baseStart_1753289 : Nat := 118140960795 + 1753289 * 2 ^ 59
def prefixEnd_1753289 : Nat := 4983230072969 + 3 ^ 40 * 1753289 * 2
def baseEnd_1753289 : Nat := 400124436995953769966345

theorem tailTrace_1753289 : CollatzResearch.WordTrace tailWord_1753289 prefixEnd_1753289 400124436995953769966345 := by
  unfold tailWord_1753289
  simp only [CollatzResearch.WordTrace]
  refine ⟨63947703345140865766838921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42631802230093910511225947 63947703345140865766838921)
  ·
    refine ⟨47960777508855649325129191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63947703345140865766838921 47960777508855649325129191)
    ·
      refine ⟨71941166263283473987693787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47960777508855649325129191 71941166263283473987693787)
      ·
        refine ⟨107911749394925210981540681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71941166263283473987693787 107911749394925210981540681)
        ·
          refine ⟨80933812046193908236155511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107911749394925210981540681 80933812046193908236155511)
          ·
            refine ⟨121400718069290862354233267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80933812046193908236155511 121400718069290862354233267)
            ·
              refine ⟨182101077103936293531349901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121400718069290862354233267 182101077103936293531349901)
              ·
                refine ⟨68287903913976110074256213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 182101077103936293531349901 68287903913976110074256213)
                ·
                  refine ⟨400124436995953769966345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 68287903913976110074256213 400124436995953769966345)
                  ·
                    rfl

theorem cell21_1753289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 9].length) (baseStart_1753289 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1753289 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1753289 prefixEnd_1753289 := by exact prefixLift 1753289
  have htrace : WordTrace (prefixWord ++ tailWord_1753289) baseStart_1753289 baseEnd_1753289 := by
    simpa [prefixWord, tailWord_1753289, baseEnd_1753289] using wordTrace_append hprefix tailTrace_1753289
  have hstable : (prefixWord ++ tailWord_1753289).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753289).length < 2 ^ (prefixWord ++ tailWord_1753289).sum := by decide
  have hdescent : baseEnd_1753289 < baseStart_1753289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753292 : List Nat := [2, 2, 1, 6, 1, 9]
def baseStart_1753292 : Nat := 118140960795 + 1753292 * 2 ^ 59
def prefixEnd_1753292 : Nat := 4983230072969 + 3 ^ 40 * 1753292 * 2
def baseEnd_1753292 : Nat := 14819448949512090052457

theorem tailTrace_1753292 : CollatzResearch.WordTrace tailWord_1753292 prefixEnd_1753292 14819448949512090052457 := by
  unfold tailWord_1753292
  simp only [CollatzResearch.WordTrace]
  refine ⟨31973906382064998639599065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42631875176086664852798753 31973906382064998639599065)
  ·
    refine ⟨23980429786548748979699299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31973906382064998639599065 23980429786548748979699299)
    ·
      refine ⟨35970644679823123469548949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23980429786548748979699299 35970644679823123469548949)
      ·
        refine ⟨1686123969366708912635107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 35970644679823123469548949 1686123969366708912635107)
        ·
          refine ⟨2529185954050063368952661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1686123969366708912635107 2529185954050063368952661)
          ·
            refine ⟨14819448949512090052457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2529185954050063368952661 14819448949512090052457)
            ·
              rfl

theorem cell21_1753292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 9].length) (baseStart_1753292 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1753292 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1753292 prefixEnd_1753292 := by exact prefixLift 1753292
  have htrace : WordTrace (prefixWord ++ tailWord_1753292) baseStart_1753292 baseEnd_1753292 := by
    simpa [prefixWord, tailWord_1753292, baseEnd_1753292] using wordTrace_append hprefix tailTrace_1753292
  have hstable : (prefixWord ++ tailWord_1753292).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753292).length < 2 ^ (prefixWord ++ tailWord_1753292).sum := by decide
  have hdescent : baseEnd_1753292 < baseStart_1753292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753309 : List Nat := [1, 4, 3, 2, 1, 3, 1, 6]
def baseStart_1753309 : Nat := 118140960795 + 1753309 * 2 ^ 59
def prefixEnd_1753309 : Nat := 4983230072969 + 3 ^ 40 * 1753309 * 2
def baseEnd_1753309 : Nat := 133376333756146059877657

theorem tailTrace_1753309 : CollatzResearch.WordTrace tailWord_1753309 prefixEnd_1753309 133376333756146059877657 := by
  unfold tailWord_1753309
  simp only [CollatzResearch.WordTrace]
  refine ⟨63948432805068409182566981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42632288536712272788377987 63948432805068409182566981)
  ·
    refine ⟨11990331150950326721731309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63948432805068409182566981 11990331150950326721731309)
    ·
      refine ⟨4496374181606372520649241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11990331150950326721731309 4496374181606372520649241)
      ·
        refine ⟨3372280636204779390486931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4496374181606372520649241 3372280636204779390486931)
        ·
          refine ⟨5058420954307169085730397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3372280636204779390486931 5058420954307169085730397)
          ·
            refine ⟨1896907857865188407148899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5058420954307169085730397 1896907857865188407148899)
            ·
              refine ⟨2845361786797782610723349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1896907857865188407148899 2845361786797782610723349)
              ·
                refine ⟨133376333756146059877657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2845361786797782610723349 133376333756146059877657)
                ·
                  rfl

theorem cell21_1753309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 6].length) (baseStart_1753309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1753309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1753309 prefixEnd_1753309 := by exact prefixLift 1753309
  have htrace : WordTrace (prefixWord ++ tailWord_1753309) baseStart_1753309 baseEnd_1753309 := by
    simpa [prefixWord, tailWord_1753309, baseEnd_1753309] using wordTrace_append hprefix tailTrace_1753309
  have hstable : (prefixWord ++ tailWord_1753309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753309).length < 2 ^ (prefixWord ++ tailWord_1753309).sum := by decide
  have hdescent : baseEnd_1753309 < baseStart_1753309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753340 : List Nat := [2, 2, 2, 1, 4, 2, 2, 3, 3]
def baseStart_1753340 : Nat := 118140960795 + 1753340 * 2 ^ 59
def prefixEnd_1753340 : Nat := 4983230072969 + 3 ^ 40 * 1753340 * 2
def baseEnd_1753340 : Nat := 400136075890789014616241

theorem tailTrace_1753340 : CollatzResearch.WordTrace tailWord_1753340 prefixEnd_1753340 400136075890789014616241 := by
  unfold tailWord_1753340
  simp only [CollatzResearch.WordTrace]
  refine ⟨31974781733978050738472737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42633042311970734317963649 31974781733978050738472737)
  ·
    refine ⟨23981086300483538053854553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31974781733978050738472737 23981086300483538053854553)
    ·
      refine ⟨17985814725362653540390915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23981086300483538053854553 17985814725362653540390915)
      ·
        refine ⟨26978722088043980310586373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17985814725362653540390915 26978722088043980310586373)
        ·
          refine ⟨5058510391508246308234945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26978722088043980310586373 5058510391508246308234945)
          ·
            refine ⟨3793882793631184731176209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5058510391508246308234945 3793882793631184731176209)
            ·
              refine ⟨2845412095223388548382157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3793882793631184731176209 2845412095223388548382157)
              ·
                refine ⟨1067029535708770705643309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2845412095223388548382157 1067029535708770705643309)
                ·
                  refine ⟨400136075890789014616241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1067029535708770705643309 400136075890789014616241)
                  ·
                    rfl

theorem cell21_1753340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 3, 3].length) (baseStart_1753340 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1753340 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1753340 prefixEnd_1753340 := by exact prefixLift 1753340
  have htrace : WordTrace (prefixWord ++ tailWord_1753340) baseStart_1753340 baseEnd_1753340 := by
    simpa [prefixWord, tailWord_1753340, baseEnd_1753340] using wordTrace_append hprefix tailTrace_1753340
  have hstable : (prefixWord ++ tailWord_1753340).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753340).length < 2 ^ (prefixWord ++ tailWord_1753340).sum := by decide
  have hdescent : baseEnd_1753340 < baseStart_1753340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753534 : List Nat := [4, 2, 1, 1, 1, 1, 3, 3, 5]
def baseStart_1753534 : Nat := 118140960795 + 1753534 * 2 ^ 59
def prefixEnd_1753534 : Nat := 4983230072969 + 3 ^ 40 * 1753534 * 2
def baseEnd_1753534 : Nat := 400180349333887788382511

theorem tailTrace_1753534 : CollatzResearch.WordTrace tailWord_1753534 prefixEnd_1753534 400180349333887788382511 := by
  unfold tailWord_1753534
  simp only [CollatzResearch.WordTrace]
  refine ⟨7994579903656659076188457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42637759486168848406338437 7994579903656659076188457)
  ·
    refine ⟨5995934927742494307141343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7994579903656659076188457 5995934927742494307141343)
    ·
      refine ⟨8993902391613741460712015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5995934927742494307141343 8993902391613741460712015)
      ·
        refine ⟨13490853587420612191068023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8993902391613741460712015 13490853587420612191068023)
        ·
          refine ⟨20236280381130918286602035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13490853587420612191068023 20236280381130918286602035)
          ·
            refine ⟨30354420571696377429903053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20236280381130918286602035 30354420571696377429903053)
            ·
              refine ⟨11382907714386141536213645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30354420571696377429903053 11382907714386141536213645)
              ·
                refine ⟨4268590392894803076080117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11382907714386141536213645 4268590392894803076080117)
                ·
                  refine ⟨400180349333887788382511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4268590392894803076080117 400180349333887788382511)
                  ·
                    rfl

theorem cell21_1753534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_1753534 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1753534 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1753534 prefixEnd_1753534 := by exact prefixLift 1753534
  have htrace : WordTrace (prefixWord ++ tailWord_1753534) baseStart_1753534 baseEnd_1753534 := by
    simpa [prefixWord, tailWord_1753534, baseEnd_1753534] using wordTrace_append hprefix tailTrace_1753534
  have hstable : (prefixWord ++ tailWord_1753534).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753534).length < 2 ^ (prefixWord ++ tailWord_1753534).sum := by decide
  have hdescent : baseEnd_1753534 < baseStart_1753534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753554 : List Nat := [3, 2, 2, 4, 1, 2, 2, 5]
def baseStart_1753554 : Nat := 118140960795 + 1753554 * 2 ^ 59
def prefixEnd_1753554 : Nat := 4983230072969 + 3 ^ 40 * 1753554 * 2
def baseEnd_1753554 : Nat := 133394971202124066016379

theorem tailTrace_1753554 : CollatzResearch.WordTrace tailWord_1753554 prefixEnd_1753554 133394971202124066016379 := by
  unfold tailWord_1753554
  simp only [CollatzResearch.WordTrace]
  refine ⟨15989342172295204006308929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42638245792787210683490477 15989342172295204006308929)
  ·
    refine ⟨11992006629221403004731697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15989342172295204006308929 11992006629221403004731697)
    ·
      refine ⟨8994004971916052253548773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11992006629221403004731697 8994004971916052253548773)
      ·
        refine ⟨1686375932234259797540395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8994004971916052253548773 1686375932234259797540395)
        ·
          refine ⟨2529563898351389696310593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1686375932234259797540395 2529563898351389696310593)
          ·
            refine ⟨1897172923763542272232945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2529563898351389696310593 1897172923763542272232945)
            ·
              refine ⟨1422879692822656704174709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1897172923763542272232945 1422879692822656704174709)
              ·
                refine ⟨133394971202124066016379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1422879692822656704174709 133394971202124066016379)
                ·
                  rfl

theorem cell21_1753554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 5].length) (baseStart_1753554 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1753554 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1753554 prefixEnd_1753554 := by exact prefixLift 1753554
  have htrace : WordTrace (prefixWord ++ tailWord_1753554) baseStart_1753554 baseEnd_1753554 := by
    simpa [prefixWord, tailWord_1753554, baseEnd_1753554] using wordTrace_append hprefix tailTrace_1753554
  have hstable : (prefixWord ++ tailWord_1753554).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753554).length < 2 ^ (prefixWord ++ tailWord_1753554).sum := by decide
  have hdescent : baseEnd_1753554 < baseStart_1753554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753613 : List Nat := [1, 7, 1, 1, 1, 1, 2, 7]
def baseStart_1753613 : Nat := 118140960795 + 1753613 * 2 ^ 59
def prefixEnd_1753613 : Nat := 4983230072969 + 3 ^ 40 * 1753613 * 2
def baseEnd_1753613 : Nat := 133399459403400402188561

theorem tailTrace_1753613 : CollatzResearch.WordTrace tailWord_1753613 prefixEnd_1753613 133399459403400402188561 := by
  unfold tailWord_1753613
  simp only [CollatzResearch.WordTrace]
  refine ⟨63959520595967069101633493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42639680397311379401088995 63959520595967069101633493)
  ·
    refine ⟨1499051263967978182069535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 63959520595967069101633493 1499051263967978182069535)
    ·
      refine ⟨2248576895951967273104303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1499051263967978182069535 2248576895951967273104303)
      ·
        refine ⟨3372865343927950909656455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2248576895951967273104303 3372865343927950909656455)
        ·
          refine ⟨5059298015891926364484683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3372865343927950909656455 5059298015891926364484683)
          ·
            refine ⟨7588947023837889546727025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5059298015891926364484683 7588947023837889546727025)
            ·
              refine ⟨5691710267878417160045269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7588947023837889546727025 5691710267878417160045269)
              ·
                refine ⟨133399459403400402188561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5691710267878417160045269 133399459403400402188561)
                ·
                  rfl

theorem cell21_1753613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 7].length) (baseStart_1753613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1753613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1753613 prefixEnd_1753613 := by exact prefixLift 1753613
  have htrace : WordTrace (prefixWord ++ tailWord_1753613) baseStart_1753613 baseEnd_1753613 := by
    simpa [prefixWord, tailWord_1753613, baseEnd_1753613] using wordTrace_append hprefix tailTrace_1753613
  have hstable : (prefixWord ++ tailWord_1753613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753613).length < 2 ^ (prefixWord ++ tailWord_1753613).sum := by decide
  have hdescent : baseEnd_1753613 < baseStart_1753613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753669 : List Nat := [1, 3, 1, 1, 1, 5, 1, 1, 7]
def baseStart_1753669 : Nat := 118140960795 + 1753669 * 2 ^ 59
def prefixEnd_1753669 : Nat := 4983230072969 + 3 ^ 40 * 1753669 * 2
def baseEnd_1753669 : Nat := 400211158173157553632235

theorem tailTrace_1753669 : CollatzResearch.WordTrace tailWord_1753669 prefixEnd_1753669 400211158173157553632235 := by
  unfold tailWord_1753669
  simp only [CollatzResearch.WordTrace]
  refine ⟨63961563083764190665672061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42641042055842793777114707 63961563083764190665672061)
  ·
    refine ⟨23985586156411571499627023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63961563083764190665672061 23985586156411571499627023)
    ·
      refine ⟨35978379234617357249440535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23985586156411571499627023 35978379234617357249440535)
      ·
        refine ⟨53967568851926035874160803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35978379234617357249440535 53967568851926035874160803)
        ·
          refine ⟨80951353277889053811241205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53967568851926035874160803 80951353277889053811241205)
          ·
            refine ⟨7589189369802098794803863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80951353277889053811241205 7589189369802098794803863)
            ·
              refine ⟨11383784054703148192205795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7589189369802098794803863 11383784054703148192205795)
              ·
                refine ⟨17075676082054722288308693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11383784054703148192205795 17075676082054722288308693)
                ·
                  refine ⟨400211158173157553632235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17075676082054722288308693 400211158173157553632235)
                  ·
                    rfl

theorem cell21_1753669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 7].length) (baseStart_1753669 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1753669 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1753669 prefixEnd_1753669 := by exact prefixLift 1753669
  have htrace : WordTrace (prefixWord ++ tailWord_1753669) baseStart_1753669 baseEnd_1753669 := by
    simpa [prefixWord, tailWord_1753669, baseEnd_1753669] using wordTrace_append hprefix tailTrace_1753669
  have hstable : (prefixWord ++ tailWord_1753669).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753669).length < 2 ^ (prefixWord ++ tailWord_1753669).sum := by decide
  have hdescent : baseEnd_1753669 < baseStart_1753669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753700 : List Nat := [2, 3, 1, 1, 2, 2, 3, 1, 6]
def baseStart_1753700 : Nat := 118140960795 + 1753700 * 2 ^ 59
def prefixEnd_1753700 : Nat := 4983230072969 + 3 ^ 40 * 1753700 * 2
def baseEnd_1753700 : Nat := 400218232795508388615505

theorem tailTrace_1753700 : CollatzResearch.WordTrace tailWord_1753700 prefixEnd_1753700 400218232795508388615505 := by
  unfold tailWord_1753700
  simp only [CollatzResearch.WordTrace]
  refine ⟨31981346873325941480025277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42641795831101255306700369 31981346873325941480025277)
  ·
    refine ⟨11993005077497228055009479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31981346873325941480025277 11993005077497228055009479)
    ·
      refine ⟨17989507616245842082514219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11993005077497228055009479 17989507616245842082514219)
      ·
        refine ⟨26984261424368763123771329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17989507616245842082514219 26984261424368763123771329)
        ·
          refine ⟨20238196068276572342828497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26984261424368763123771329 20238196068276572342828497)
          ·
            refine ⟨15178647051207429257121373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20238196068276572342828497 15178647051207429257121373)
            ·
              refine ⟨5691992644202785971420515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15178647051207429257121373 5691992644202785971420515)
              ·
                refine ⟨8537988966304178957130773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5691992644202785971420515 8537988966304178957130773)
                ·
                  refine ⟨400218232795508388615505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8537988966304178957130773 400218232795508388615505)
                  ·
                    rfl

theorem cell21_1753700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_1753700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1753700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1753700 prefixEnd_1753700 := by exact prefixLift 1753700
  have htrace : WordTrace (prefixWord ++ tailWord_1753700) baseStart_1753700 baseEnd_1753700 := by
    simpa [prefixWord, tailWord_1753700, baseEnd_1753700] using wordTrace_append hprefix tailTrace_1753700
  have hstable : (prefixWord ++ tailWord_1753700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753700).length < 2 ^ (prefixWord ++ tailWord_1753700).sum := by decide
  have hdescent : baseEnd_1753700 < baseStart_1753700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753731 : List Nat := [1, 1, 1, 3, 3, 1, 6, 5]
def baseStart_1753731 : Nat := 118140960795 + 1753731 * 2 ^ 59
def prefixEnd_1753731 : Nat := 4983230072969 + 3 ^ 40 * 1753731 * 2
def baseEnd_1753731 : Nat := 133408435805953074532925

theorem tailTrace_1753731 : CollatzResearch.WordTrace tailWord_1753731 prefixEnd_1753731 133408435805953074532925 := by
  unfold tailWord_1753731
  simp only [CollatzResearch.WordTrace]
  refine ⟨63963824409539575254429047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42642549606359716836286031 63963824409539575254429047)
  ·
    refine ⟨95945736614309362881643571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63963824409539575254429047 95945736614309362881643571)
    ·
      refine ⟨143918604921464044322465357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95945736614309362881643571 143918604921464044322465357)
      ·
        refine ⟨53969476845549016620924509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143918604921464044322465357 53969476845549016620924509)
        ·
          refine ⟨20238553817080881232846691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53969476845549016620924509 20238553817080881232846691)
          ·
            refine ⟨30357830725621321849270037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20238553817080881232846691 30357830725621321849270037)
            ·
              refine ⟨1423023315263499461684533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30357830725621321849270037 1423023315263499461684533)
              ·
                refine ⟨133408435805953074532925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1423023315263499461684533 133408435805953074532925)
                ·
                  rfl

theorem cell21_1753731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 5].length) (baseStart_1753731 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1753731 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1753731 prefixEnd_1753731 := by exact prefixLift 1753731
  have htrace : WordTrace (prefixWord ++ tailWord_1753731) baseStart_1753731 baseEnd_1753731 := by
    simpa [prefixWord, tailWord_1753731, baseEnd_1753731] using wordTrace_append hprefix tailTrace_1753731
  have hstable : (prefixWord ++ tailWord_1753731).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753731).length < 2 ^ (prefixWord ++ tailWord_1753731).sum := by decide
  have hdescent : baseEnd_1753731 < baseStart_1753731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753748 : List Nat := [2, 4, 2, 2, 1, 3, 7]
def baseStart_1753748 : Nat := 118140960795 + 1753748 * 2 ^ 59
def prefixEnd_1753748 : Nat := 4983230072969 + 3 ^ 40 * 1753748 * 2
def baseEnd_1753748 : Nat := 44469909672163441312823

theorem tailTrace_1753748 : CollatzResearch.WordTrace tailWord_1753748 prefixEnd_1753748 44469909672163441312823 := by
  unfold tailWord_1753748
  simp only [CollatzResearch.WordTrace]
  refine ⟨31982222225238993578898949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42642962966985324771865265 31982222225238993578898949)
  ·
    refine ⟨5996666667232311296043553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31982222225238993578898949 5996666667232311296043553)
    ·
      refine ⟨4497500000424233472032665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5996666667232311296043553 4497500000424233472032665)
      ·
        refine ⟨3373125000318175104024499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4497500000424233472032665 3373125000318175104024499)
        ·
          refine ⟨5059687500477262656036749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3373125000318175104024499 5059687500477262656036749)
          ·
            refine ⟨1897382812678973496013781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5059687500477262656036749 1897382812678973496013781)
            ·
              refine ⟨44469909672163441312823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1897382812678973496013781 44469909672163441312823)
              ·
                rfl

theorem cell21_1753748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 7].length) (baseStart_1753748 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1753748 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1753748 prefixEnd_1753748 := by exact prefixLift 1753748
  have htrace : WordTrace (prefixWord ++ tailWord_1753748) baseStart_1753748 baseEnd_1753748 := by
    simpa [prefixWord, tailWord_1753748, baseEnd_1753748] using wordTrace_append hprefix tailTrace_1753748
  have hstable : (prefixWord ++ tailWord_1753748).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753748).length < 2 ^ (prefixWord ++ tailWord_1753748).sum := by decide
  have hdescent : baseEnd_1753748 < baseStart_1753748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753810 : List Nat := [3, 2, 2, 2, 3, 1, 2, 2, 4]
def baseStart_1753810 : Nat := 118140960795 + 1753810 * 2 ^ 59
def prefixEnd_1753810 : Nat := 4983230072969 + 3 ^ 40 * 1753810 * 2
def baseEnd_1753810 : Nat := 400243336294172641781947

theorem tailTrace_1753810 : CollatzResearch.WordTrace tailWord_1753810 prefixEnd_1753810 400243336294172641781947 := by
  unfold tailWord_1753810
  simp only [CollatzResearch.WordTrace]
  refine ⟨15991676444063342936638721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42644470517502247831036589 15991676444063342936638721)
  ·
    refine ⟨11993757333047507202479041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15991676444063342936638721 11993757333047507202479041)
    ·
      refine ⟨8995317999785630401859281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11993757333047507202479041 8995317999785630401859281)
      ·
        refine ⟨6746488499839222801394461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8995317999785630401859281 6746488499839222801394461)
        ·
          refine ⟨2529933187439708550522923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6746488499839222801394461 2529933187439708550522923)
          ·
            refine ⟨3794899781159562825784385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2529933187439708550522923 3794899781159562825784385)
            ·
              refine ⟨2846174835869672119338289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3794899781159562825784385 2846174835869672119338289)
              ·
                refine ⟨2134631126902254089503717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2846174835869672119338289 2134631126902254089503717)
                ·
                  refine ⟨400243336294172641781947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2134631126902254089503717 400243336294172641781947)
                  ·
                    rfl

theorem cell21_1753810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_1753810 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1753810 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1753810 prefixEnd_1753810 := by exact prefixLift 1753810
  have htrace : WordTrace (prefixWord ++ tailWord_1753810) baseStart_1753810 baseEnd_1753810 := by
    simpa [prefixWord, tailWord_1753810, baseEnd_1753810] using wordTrace_append hprefix tailTrace_1753810
  have hstable : (prefixWord ++ tailWord_1753810).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753810).length < 2 ^ (prefixWord ++ tailWord_1753810).sum := by decide
  have hdescent : baseEnd_1753810 < baseStart_1753810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753835 : List Nat := [1, 1, 1, 1, 2, 4, 1, 2, 8]
def baseStart_1753835 : Nat := 118140960795 + 1753835 * 2 ^ 59
def prefixEnd_1753835 : Nat := 4983230072969 + 3 ^ 40 * 1753835 * 2
def baseEnd_1753835 : Nat := 400249041634778153865229

theorem tailTrace_1753835 : CollatzResearch.WordTrace tailWord_1753835 prefixEnd_1753835 400249041634778153865229 := by
  unfold tailWord_1753835
  simp only [CollatzResearch.WordTrace]
  refine ⟨63967617601162801016214959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42645078400775200677476639 63967617601162801016214959)
  ·
    refine ⟨95951426401744201524322439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63967617601162801016214959 95951426401744201524322439)
    ·
      refine ⟨143927139602616302286483659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95951426401744201524322439 143927139602616302286483659)
      ·
        refine ⟨215890709403924453429725489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143927139602616302286483659 215890709403924453429725489)
        ·
          refine ⟨161918032052943340072294117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215890709403924453429725489 161918032052943340072294117)
          ·
            refine ⟨30359631009926876263555147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161918032052943340072294117 30359631009926876263555147)
            ·
              refine ⟨45539446514890314395332721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30359631009926876263555147 45539446514890314395332721)
              ·
                refine ⟨34154584886167735796499541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45539446514890314395332721 34154584886167735796499541)
                ·
                  refine ⟨400249041634778153865229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34154584886167735796499541 400249041634778153865229)
                  ·
                    rfl

theorem cell21_1753835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 8].length) (baseStart_1753835 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1753835 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1753835 prefixEnd_1753835 := by exact prefixLift 1753835
  have htrace : WordTrace (prefixWord ++ tailWord_1753835) baseStart_1753835 baseEnd_1753835 := by
    simpa [prefixWord, tailWord_1753835, baseEnd_1753835] using wordTrace_append hprefix tailTrace_1753835
  have hstable : (prefixWord ++ tailWord_1753835).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753835).length < 2 ^ (prefixWord ++ tailWord_1753835).sum := by decide
  have hdescent : baseEnd_1753835 < baseStart_1753835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753838 : List Nat := [4, 1, 2, 1, 1, 4, 1, 2, 5]
def baseStart_1753838 : Nat := 118140960795 + 1753838 * 2 ^ 59
def prefixEnd_1753838 : Nat := 4983230072969 + 3 ^ 40 * 1753838 * 2
def baseEnd_1753838 : Nat := 400249726275650815315223

theorem tailTrace_1753838 : CollatzResearch.WordTrace tailWord_1753838 prefixEnd_1753838 400249726275650815315223 := by
  unfold tailWord_1753838
  simp only [CollatzResearch.WordTrace]
  refine ⟨7995965877518991566071771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42645151346767955019049445 7995965877518991566071771)
  ·
    refine ⟨11993948816278487349107657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7995965877518991566071771 11993948816278487349107657)
    ·
      refine ⟨8995461612208865511830743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11993948816278487349107657 8995461612208865511830743)
      ·
        refine ⟨13493192418313298267746115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8995461612208865511830743 13493192418313298267746115)
        ·
          refine ⟨20239788627469947401619173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13493192418313298267746115 20239788627469947401619173)
          ·
            refine ⟨3794960367650615137803595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20239788627469947401619173 3794960367650615137803595)
            ·
              refine ⟨5692440551475922706705393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3794960367650615137803595 5692440551475922706705393)
              ·
                refine ⟨4269330413606942030029045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5692440551475922706705393 4269330413606942030029045)
                ·
                  refine ⟨400249726275650815315223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4269330413606942030029045 400249726275650815315223)
                  ·
                    rfl

theorem cell21_1753838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_1753838 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1753838 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1753838 prefixEnd_1753838 := by exact prefixLift 1753838
  have htrace : WordTrace (prefixWord ++ tailWord_1753838) baseStart_1753838 baseEnd_1753838 := by
    simpa [prefixWord, tailWord_1753838, baseEnd_1753838] using wordTrace_append hprefix tailTrace_1753838
  have hstable : (prefixWord ++ tailWord_1753838).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753838).length < 2 ^ (prefixWord ++ tailWord_1753838).sum := by decide
  have hdescent : baseEnd_1753838 < baseStart_1753838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753866 : List Nat := [3, 1, 2, 2, 1, 2, 10]
def baseStart_1753866 : Nat := 118140960795 + 1753866 * 2 ^ 59
def prefixEnd_1753866 : Nat := 4983230072969 + 3 ^ 40 * 1753866 * 2
def baseEnd_1753866 : Nat := 44472901806347665427611

theorem tailTrace_1753866 : CollatzResearch.WordTrace tailWord_1753866 prefixEnd_1753866 44472901806347665427611 := by
  unfold tailWord_1753866
  simp only [CollatzResearch.WordTrace]
  refine ⟨15992187066012623327648363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42645832176033662207062301 15992187066012623327648363)
  ·
    refine ⟨23988280599018934991472545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15992187066012623327648363 23988280599018934991472545)
    ·
      refine ⟨17991210449264201243604409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23988280599018934991472545 17991210449264201243604409)
      ·
        refine ⟨13493407836948150932703307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17991210449264201243604409 13493407836948150932703307)
        ·
          refine ⟨20240111755422226399054961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13493407836948150932703307 20240111755422226399054961)
          ·
            refine ⟨15180083816566669799291221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20240111755422226399054961 15180083816566669799291221)
            ·
              refine ⟨44472901806347665427611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15180083816566669799291221 44472901806347665427611)
              ·
                rfl

theorem cell21_1753866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 10].length) (baseStart_1753866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1753866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1753866 prefixEnd_1753866 := by exact prefixLift 1753866
  have htrace : WordTrace (prefixWord ++ tailWord_1753866) baseStart_1753866 baseEnd_1753866 := by
    simpa [prefixWord, tailWord_1753866, baseEnd_1753866] using wordTrace_append hprefix tailTrace_1753866
  have hstable : (prefixWord ++ tailWord_1753866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753866).length < 2 ^ (prefixWord ++ tailWord_1753866).sum := by decide
  have hdescent : baseEnd_1753866 < baseStart_1753866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753911 : List Nat := [1, 1, 3, 1, 2, 1, 3, 1, 8]
def baseStart_1753911 : Nat := 118140960795 + 1753911 * 2 ^ 59
def prefixEnd_1753911 : Nat := 4983230072969 + 3 ^ 40 * 1753911 * 2
def baseEnd_1753911 : Nat := 400266385870218910598407

theorem tailTrace_1753911 : CollatzResearch.WordTrace tailWord_1753911 prefixEnd_1753911 400266385870218910598407 := by
  unfold tailWord_1753911
  simp only [CollatzResearch.WordTrace]
  refine ⟨63970389548887465995981587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42646926365924977330654391 63970389548887465995981587)
  ·
    refine ⟨95955584323331198993972381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63970389548887465995981587 95955584323331198993972381)
    ·
      refine ⟨35983344121249199622739643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95955584323331198993972381 35983344121249199622739643)
      ·
        refine ⟨53975016181873799434109465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35983344121249199622739643 53975016181873799434109465)
        ·
          refine ⟨40481262136405349575582099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53975016181873799434109465 40481262136405349575582099)
          ·
            refine ⟨60721893204608024363373149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40481262136405349575582099 60721893204608024363373149)
            ·
              refine ⟨22770709951728009136264931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60721893204608024363373149 22770709951728009136264931)
              ·
                refine ⟨34156064927592013704397397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22770709951728009136264931 34156064927592013704397397)
                ·
                  refine ⟨400266385870218910598407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34156064927592013704397397 400266385870218910598407)
                  ·
                    rfl

theorem cell21_1753911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 8].length) (baseStart_1753911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1753911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1753911 prefixEnd_1753911 := by exact prefixLift 1753911
  have htrace : WordTrace (prefixWord ++ tailWord_1753911) baseStart_1753911 baseEnd_1753911 := by
    simpa [prefixWord, tailWord_1753911, baseEnd_1753911] using wordTrace_append hprefix tailTrace_1753911
  have hstable : (prefixWord ++ tailWord_1753911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753911).length < 2 ^ (prefixWord ++ tailWord_1753911).sum := by decide
  have hdescent : baseEnd_1753911 < baseStart_1753911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753928 : List Nat := [2, 1, 3, 1, 1, 3, 2, 4, 4]
def baseStart_1753928 : Nat := 118140960795 + 1753928 * 2 ^ 59
def prefixEnd_1753928 : Nat := 4983230072969 + 3 ^ 40 * 1753928 * 2
def baseEnd_1753928 : Nat := 400270265501830658815039

theorem tailTrace_1753928 : CollatzResearch.WordTrace tailWord_1753928 prefixEnd_1753928 400270265501830658815039 := by
  unfold tailWord_1753928
  simp only [CollatzResearch.WordTrace]
  refine ⟨31985504794912938949675219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42647339726550585266233625 31985504794912938949675219)
  ·
    refine ⟨47978257192369408424512829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31985504794912938949675219 47978257192369408424512829)
    ·
      refine ⟨17991846447138528159192311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47978257192369408424512829 17991846447138528159192311)
      ·
        refine ⟨26987769670707792238788467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17991846447138528159192311 26987769670707792238788467)
        ·
          refine ⟨40481654506061688358182701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26987769670707792238788467 40481654506061688358182701)
          ·
            refine ⟨15180620439773133134318513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40481654506061688358182701 15180620439773133134318513)
            ·
              refine ⟨11385465329829849850738885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15180620439773133134318513 11385465329829849850738885)
              ·
                refine ⟨2134774749343096847013541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11385465329829849850738885 2134774749343096847013541)
                ·
                  refine ⟨400270265501830658815039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2134774749343096847013541 400270265501830658815039)
                  ·
                    rfl

theorem cell21_1753928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 4, 4].length) (baseStart_1753928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1753928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1753928 prefixEnd_1753928 := by exact prefixLift 1753928
  have htrace : WordTrace (prefixWord ++ tailWord_1753928) baseStart_1753928 baseEnd_1753928 := by
    simpa [prefixWord, tailWord_1753928, baseEnd_1753928] using wordTrace_append hprefix tailTrace_1753928
  have hstable : (prefixWord ++ tailWord_1753928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753928).length < 2 ^ (prefixWord ++ tailWord_1753928).sum := by decide
  have hdescent : baseEnd_1753928 < baseStart_1753928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753945 : List Nat := [1, 2, 1, 2, 2, 4, 4, 1, 4]
def baseStart_1753945 : Nat := 118140960795 + 1753945 * 2 ^ 59
def prefixEnd_1753945 : Nat := 4983230072969 + 3 ^ 40 * 1753945 * 2
def baseEnd_1753945 : Nat := 400274145133442407031671

theorem tailTrace_1753945 : CollatzResearch.WordTrace tailWord_1753945 prefixEnd_1753945 400274145133442407031671 := by
  unfold tailWord_1753945
  simp only [CollatzResearch.WordTrace]
  refine ⟨63971629630764289802719289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42647753087176193201812859 63971629630764289802719289)
  ·
    refine ⟨47978722223073217352039467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63971629630764289802719289 47978722223073217352039467)
    ·
      refine ⟨71968083334609826028059201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47978722223073217352039467 71968083334609826028059201)
      ·
        refine ⟨53976062500957369521044401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71968083334609826028059201 53976062500957369521044401)
        ·
          refine ⟨40482046875718027140783301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53976062500957369521044401 40482046875718027140783301)
          ·
            refine ⟨7590383789197130088896869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40482046875718027140783301 7590383789197130088896869)
            ·
              refine ⟨1423196960474461891668163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7590383789197130088896869 1423196960474461891668163)
              ·
                refine ⟨2134795440711692837502245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1423196960474461891668163 2134795440711692837502245)
                ·
                  refine ⟨400274145133442407031671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2134795440711692837502245 400274145133442407031671)
                  ·
                    rfl

theorem cell21_1753945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 1, 4].length) (baseStart_1753945 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1753945 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1753945 prefixEnd_1753945 := by exact prefixLift 1753945
  have htrace : WordTrace (prefixWord ++ tailWord_1753945) baseStart_1753945 baseEnd_1753945 := by
    simpa [prefixWord, tailWord_1753945, baseEnd_1753945] using wordTrace_append hprefix tailTrace_1753945
  have hstable : (prefixWord ++ tailWord_1753945).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753945).length < 2 ^ (prefixWord ++ tailWord_1753945).sum := by decide
  have hdescent : baseEnd_1753945 < baseStart_1753945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1753982 : List Nat := [4, 2, 3, 1, 2, 2, 2, 2, 3]
def baseStart_1753982 : Nat := 118140960795 + 1753982 * 2 ^ 59
def prefixEnd_1753982 : Nat := 4983230072969 + 3 ^ 40 * 1753982 * 2
def baseEnd_1753982 : Nat := 400282589037538564914929

theorem tailTrace_1753982 : CollatzResearch.WordTrace tailWord_1753982 prefixEnd_1753982 400282589037538564914929 := by
  unfold tailWord_1753982
  simp only [CollatzResearch.WordTrace]
  refine ⟨7996622391453780640227025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42648652754420163414544133 7996622391453780640227025)
  ·
    refine ⟨5997466793590335480170269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7996622391453780640227025 5997466793590335480170269)
    ·
      refine ⟨2249050047596375805063851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5997466793590335480170269 2249050047596375805063851)
      ·
        refine ⟨3373575071394563707595777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2249050047596375805063851 3373575071394563707595777)
        ·
          refine ⟨2530181303545922780696833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3373575071394563707595777 2530181303545922780696833)
          ·
            refine ⟨1897635977659442085522625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2530181303545922780696833 1897635977659442085522625)
            ·
              refine ⟨1423226983244581564141969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1897635977659442085522625 1423226983244581564141969)
              ·
                refine ⟨1067420237433436173106477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1423226983244581564141969 1067420237433436173106477)
                ·
                  refine ⟨400282589037538564914929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1067420237433436173106477 400282589037538564914929)
                  ·
                    rfl

theorem cell21_1753982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_1753982 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1753982 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1753982 prefixEnd_1753982 := by exact prefixLift 1753982
  have htrace : WordTrace (prefixWord ++ tailWord_1753982) baseStart_1753982 baseEnd_1753982 := by
    simpa [prefixWord, tailWord_1753982, baseEnd_1753982] using wordTrace_append hprefix tailTrace_1753982
  have hstable : (prefixWord ++ tailWord_1753982).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1753982).length < 2 ^ (prefixWord ++ tailWord_1753982).sum := by decide
  have hdescent : baseEnd_1753982 < baseStart_1753982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1753982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754066 : List Nat := [3, 2, 2, 3, 1, 1, 2, 2, 5]
def baseStart_1754066 : Nat := 118140960795 + 1754066 * 2 ^ 59
def prefixEnd_1754066 : Nat := 4983230072969 + 3 ^ 40 * 1754066 * 2
def baseEnd_1754066 : Nat := 400301758981973085514757

theorem tailTrace_1754066 : CollatzResearch.WordTrace tailWord_1754066 prefixEnd_1754066 400301758981973085514757 := by
  unfold tailWord_1754066
  simp only [CollatzResearch.WordTrace]
  refine ⟨15994010715831481866968513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42650695242217284978582701 15994010715831481866968513)
  ·
    refine ⟨11995508036873611400226385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15994010715831481866968513 11995508036873611400226385)
    ·
      refine ⟨8996631027655208550169789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11995508036873611400226385 8996631027655208550169789)
      ·
        refine ⟨3373736635370703206313671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8996631027655208550169789 3373736635370703206313671)
        ·
          refine ⟨5060604953056054809470507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3373736635370703206313671 5060604953056054809470507)
          ·
            refine ⟨7590907429584082214205761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5060604953056054809470507 7590907429584082214205761)
            ·
              refine ⟨5693180572188061660654321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7590907429584082214205761 5693180572188061660654321)
              ·
                refine ⟨4269885429141046245490741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5693180572188061660654321 4269885429141046245490741)
                ·
                  refine ⟨400301758981973085514757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4269885429141046245490741 400301758981973085514757)
                  ·
                    rfl

theorem cell21_1754066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_1754066 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1754066 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1754066 prefixEnd_1754066 := by exact prefixLift 1754066
  have htrace : WordTrace (prefixWord ++ tailWord_1754066) baseStart_1754066 baseEnd_1754066 := by
    simpa [prefixWord, tailWord_1754066, baseEnd_1754066] using wordTrace_append hprefix tailTrace_1754066
  have hstable : (prefixWord ++ tailWord_1754066).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754066).length < 2 ^ (prefixWord ++ tailWord_1754066).sum := by decide
  have hdescent : baseEnd_1754066 < baseStart_1754066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754069 : List Nat := [1, 3, 2, 3, 4, 1, 2, 5]
def baseStart_1754069 : Nat := 118140960795 + 1754069 * 2 ^ 59
def prefixEnd_1754069 : Nat := 4983230072969 + 3 ^ 40 * 1754069 * 2
def baseEnd_1754069 : Nat := 133434147874281915654917

theorem tailTrace_1754069 : CollatzResearch.WordTrace tailWord_1754069 prefixEnd_1754069 133434147874281915654917 := by
  unfold tailWord_1754069
  simp only [CollatzResearch.WordTrace]
  refine ⟨63976152282315058980233261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42650768188210039320155507 63976152282315058980233261)
  ·
    refine ⟨23991057105868147117587473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63976152282315058980233261 23991057105868147117587473)
    ·
      refine ⟨17993292829401110338190605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23991057105868147117587473 17993292829401110338190605)
      ·
        refine ⟨6747484811025416376821477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17993292829401110338190605 6747484811025416376821477)
        ·
          refine ⟨1265153402067265570654027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6747484811025416376821477 1265153402067265570654027)
          ·
            refine ⟨1897730103100898355981041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1265153402067265570654027 1897730103100898355981041)
            ·
              refine ⟨1423297577325673766985781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1897730103100898355981041 1423297577325673766985781)
              ·
                refine ⟨133434147874281915654917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1423297577325673766985781 133434147874281915654917)
                ·
                  rfl

theorem cell21_1754069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 5].length) (baseStart_1754069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1754069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1754069 prefixEnd_1754069 := by exact prefixLift 1754069
  have htrace : WordTrace (prefixWord ++ tailWord_1754069) baseStart_1754069 baseEnd_1754069 := by
    simpa [prefixWord, tailWord_1754069, baseEnd_1754069] using wordTrace_append hprefix tailTrace_1754069
  have hstable : (prefixWord ++ tailWord_1754069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754069).length < 2 ^ (prefixWord ++ tailWord_1754069).sum := by decide
  have hdescent : baseEnd_1754069 < baseStart_1754069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754156 : List Nat := [2, 2, 1, 1, 1, 2, 6, 2, 4]
def baseStart_1754156 : Nat := 118140960795 + 1754156 * 2 ^ 59
def prefixEnd_1754156 : Nat := 4983230072969 + 3 ^ 40 * 1754156 * 2
def baseEnd_1754156 : Nat := 400322298208152929014573

theorem tailTrace_1754156 : CollatzResearch.WordTrace tailWord_1754156 prefixEnd_1754156 400322298208152929014573 := by
  unfold tailWord_1754156
  simp only [CollatzResearch.WordTrace]
  refine ⟨31989662716499936419325161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42652883621999915225766881 31989662716499936419325161)
  ·
    refine ⟨23992247037374952314493871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31989662716499936419325161 23992247037374952314493871)
    ·
      refine ⟨35988370556062428471740807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23992247037374952314493871 35988370556062428471740807)
      ·
        refine ⟨53982555834093642707611211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35988370556062428471740807 53982555834093642707611211)
        ·
          refine ⟨80973833751140464061416817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53982555834093642707611211 80973833751140464061416817)
          ·
            refine ⟨60730375313355348046062613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80973833751140464061416817 60730375313355348046062613)
            ·
              refine ⟨2846736342813531939659185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 60730375313355348046062613 2846736342813531939659185)
              ·
                refine ⟨2135052257110148954744389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2846736342813531939659185 2135052257110148954744389)
                ·
                  refine ⟨400322298208152929014573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2135052257110148954744389 400322298208152929014573)
                  ·
                    rfl

theorem cell21_1754156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 4].length) (baseStart_1754156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1754156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1754156 prefixEnd_1754156 := by exact prefixLift 1754156
  have htrace : WordTrace (prefixWord ++ tailWord_1754156) baseStart_1754156 baseEnd_1754156 := by
    simpa [prefixWord, tailWord_1754156, baseEnd_1754156] using wordTrace_append hprefix tailTrace_1754156
  have hstable : (prefixWord ++ tailWord_1754156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754156).length < 2 ^ (prefixWord ++ tailWord_1754156).sum := by decide
  have hdescent : baseEnd_1754156 < baseStart_1754156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754170 : List Nat := [3, 1, 1, 1, 3, 1, 5, 6]
def baseStart_1754170 : Nat := 118140960795 + 1754170 * 2 ^ 59
def prefixEnd_1754170 : Nat := 4983230072969 + 3 ^ 40 * 1754170 * 2
def baseEnd_1754170 : Nat := 133441831066297338593737

theorem tailTrace_1754170 : CollatzResearch.WordTrace tailWord_1754170 prefixEnd_1754170 133441831066297338593737 := by
  unfold tailWord_1754170
  simp only [CollatzResearch.WordTrace]
  refine ⟨15994959013737288307414991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42653224036632768819773309 15994959013737288307414991)
  ·
    refine ⟨23992438520605932461122487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15994959013737288307414991 23992438520605932461122487)
    ·
      refine ⟨35988657780908898691683731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23992438520605932461122487 35988657780908898691683731)
      ·
        refine ⟨53982986671363348037525597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35988657780908898691683731 53982986671363348037525597)
        ·
          refine ⟨20243620001761255514072099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53982986671363348037525597 20243620001761255514072099)
          ·
            refine ⟨30365430002641883271108149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20243620001761255514072099 30365430002641883271108149)
            ·
              refine ⟨2846759062747676556666389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30365430002641883271108149 2846759062747676556666389)
              ·
                refine ⟨133441831066297338593737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2846759062747676556666389 133441831066297338593737)
                ·
                  rfl

theorem cell21_1754170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 6].length) (baseStart_1754170 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1754170 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1754170 prefixEnd_1754170 := by exact prefixLift 1754170
  have htrace : WordTrace (prefixWord ++ tailWord_1754170) baseStart_1754170 baseEnd_1754170 := by
    simpa [prefixWord, tailWord_1754170, baseEnd_1754170] using wordTrace_append hprefix tailTrace_1754170
  have hstable : (prefixWord ++ tailWord_1754170).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754170).length < 2 ^ (prefixWord ++ tailWord_1754170).sum := by decide
  have hdescent : baseEnd_1754170 < baseStart_1754170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754218 : List Nat := [3, 1, 3, 2, 2, 2, 2, 1, 5]
def baseStart_1754218 : Nat := 118140960795 + 1754218 * 2 ^ 59
def prefixEnd_1754218 : Nat := 4983230072969 + 3 ^ 40 * 1754218 * 2
def baseEnd_1754218 : Nat := 400336447452854598981113

theorem tailTrace_1754218 : CollatzResearch.WordTrace tailWord_1754218 prefixEnd_1754218 400336447452854598981113 := by
  unfold tailWord_1754218
  simp only [CollatzResearch.WordTrace]
  refine ⟨15995396689693814356851827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42654391172516838284938205 15995396689693814356851827)
  ·
    refine ⟨23993095034540721535277741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15995396689693814356851827 23993095034540721535277741)
    ·
      refine ⟨8997410637952770575729153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23993095034540721535277741 8997410637952770575729153)
      ·
        refine ⟨6748057978464577931796865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8997410637952770575729153 6748057978464577931796865)
        ·
          refine ⟨5061043483848433448847649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6748057978464577931796865 5061043483848433448847649)
          ·
            refine ⟨3795782612886325086635737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5061043483848433448847649 3795782612886325086635737)
            ·
              refine ⟨2846836959664743814976803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3795782612886325086635737 2846836959664743814976803)
              ·
                refine ⟨4270255439497115722465205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2846836959664743814976803 4270255439497115722465205)
                ·
                  refine ⟨400336447452854598981113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4270255439497115722465205 400336447452854598981113)
                  ·
                    rfl

theorem cell21_1754218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 5].length) (baseStart_1754218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1754218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1754218 prefixEnd_1754218 := by exact prefixLift 1754218
  have htrace : WordTrace (prefixWord ++ tailWord_1754218) baseStart_1754218 baseEnd_1754218 := by
    simpa [prefixWord, tailWord_1754218, baseEnd_1754218] using wordTrace_append hprefix tailTrace_1754218
  have hstable : (prefixWord ++ tailWord_1754218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754218).length < 2 ^ (prefixWord ++ tailWord_1754218).sum := by decide
  have hdescent : baseEnd_1754218 < baseStart_1754218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754277 : List Nat := [1, 3, 1, 2, 1, 4, 3, 1, 5]
def baseStart_1754277 : Nat := 118140960795 + 1754277 * 2 ^ 59
def prefixEnd_1754277 : Nat := 4983230072969 + 3 ^ 40 * 1754277 * 2
def baseEnd_1754277 : Nat := 400349912056683607497659

theorem tailTrace_1754277 : CollatzResearch.WordTrace tailWord_1754277 prefixEnd_1754277 400349912056683607497659 := by
  unfold tailWord_1754277
  simp only [CollatzResearch.WordTrace]
  refine ⟨63983738665561510503805085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42655825777041007002536723 63983738665561510503805085)
  ·
    refine ⟨23993901999585566438926907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63983738665561510503805085 23993901999585566438926907)
    ·
      refine ⟨35990852999378349658390361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23993901999585566438926907 35990852999378349658390361)
      ·
        refine ⟨26993139749533762243792771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35990852999378349658390361 26993139749533762243792771)
        ·
          refine ⟨40489709624300643365689157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26993139749533762243792771 40489709624300643365689157)
          ·
            refine ⟨7591820554556370631066717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40489709624300643365689157 7591820554556370631066717)
            ·
              refine ⟨2846932707958638986650019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7591820554556370631066717 2846932707958638986650019)
              ·
                refine ⟨4270399061937958479975029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2846932707958638986650019 4270399061937958479975029)
                ·
                  refine ⟨400349912056683607497659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4270399061937958479975029 400349912056683607497659)
                  ·
                    rfl

theorem cell21_1754277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 5].length) (baseStart_1754277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1754277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1754277 prefixEnd_1754277 := by exact prefixLift 1754277
  have htrace : WordTrace (prefixWord ++ tailWord_1754277) baseStart_1754277 baseEnd_1754277 := by
    simpa [prefixWord, tailWord_1754277, baseEnd_1754277] using wordTrace_append hprefix tailTrace_1754277
  have hstable : (prefixWord ++ tailWord_1754277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754277).length < 2 ^ (prefixWord ++ tailWord_1754277).sum := by decide
  have hdescent : baseEnd_1754277 < baseStart_1754277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754325 : List Nat := [1, 3, 2, 4, 1, 2, 2, 2, 4]
def baseStart_1754325 : Nat := 118140960795 + 1754325 * 2 ^ 59
def prefixEnd_1754325 : Nat := 4983230072969 + 3 ^ 40 * 1754325 * 2
def baseEnd_1754325 : Nat := 400360866310646190697561

theorem tailTrace_1754325 : CollatzResearch.WordTrace tailWord_1754325 prefixEnd_1754325 400360866310646190697561 := by
  unfold tailWord_1754325
  simp only [CollatzResearch.WordTrace]
  refine ⟨63985489369387614701552429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42656992912925076467701619 63985489369387614701552429)
  ·
    refine ⟨23994558513520355513082161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63985489369387614701552429 23994558513520355513082161)
    ·
      refine ⟨17995918885140266634811621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23994558513520355513082161 17995918885140266634811621)
      ·
        refine ⟨3374234790963799994027179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17995918885140266634811621 3374234790963799994027179)
        ·
          refine ⟨5061352186445699991040769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3374234790963799994027179 5061352186445699991040769)
          ·
            refine ⟨3796014139834274993280577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5061352186445699991040769 3796014139834274993280577)
            ·
              refine ⟨2847010604875706244960433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3796014139834274993280577 2847010604875706244960433)
              ·
                refine ⟨2135257953656779683720325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2847010604875706244960433 2135257953656779683720325)
                ·
                  refine ⟨400360866310646190697561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2135257953656779683720325 400360866310646190697561)
                  ·
                    rfl

theorem cell21_1754325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 2, 4].length) (baseStart_1754325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1754325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1754325 prefixEnd_1754325 := by exact prefixLift 1754325
  have htrace : WordTrace (prefixWord ++ tailWord_1754325) baseStart_1754325 baseEnd_1754325 := by
    simpa [prefixWord, tailWord_1754325, baseEnd_1754325] using wordTrace_append hprefix tailTrace_1754325
  have hstable : (prefixWord ++ tailWord_1754325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754325).length < 2 ^ (prefixWord ++ tailWord_1754325).sum := by decide
  have hdescent : baseEnd_1754325 < baseStart_1754325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754328 : List Nat := [2, 1, 2, 2, 5, 2, 2, 2, 3]
def baseStart_1754328 : Nat := 118140960795 + 1754328 * 2 ^ 59
def prefixEnd_1754328 : Nat := 4983230072969 + 3 ^ 40 * 1754328 * 2
def baseEnd_1754328 : Nat := 400361550951518852147555

theorem tailTrace_1754328 : CollatzResearch.WordTrace tailWord_1754328 prefixEnd_1754328 400361550951518852147555 := by
  unfold tailWord_1754328
  simp only [CollatzResearch.WordTrace]
  refine ⟨31992799394188373106955819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42657065858917830809274425 31992799394188373106955819)
  ·
    refine ⟨47989199091282559660433729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31992799394188373106955819 47989199091282559660433729)
    ·
      refine ⟨35991899318461919745325297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47989199091282559660433729 35991899318461919745325297)
      ·
        refine ⟨26993924488846439808993973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35991899318461919745325297 26993924488846439808993973)
        ·
          refine ⟨2530680420829353732093185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26993924488846439808993973 2530680420829353732093185)
          ·
            refine ⟨1898010315622015299069889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2530680420829353732093185 1898010315622015299069889)
            ·
              refine ⟨1423507736716511474302417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1898010315622015299069889 1423507736716511474302417)
              ·
                refine ⟨1067630802537383605726813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1423507736716511474302417 1067630802537383605726813)
                ·
                  refine ⟨400361550951518852147555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1067630802537383605726813 400361550951518852147555)
                  ·
                    rfl

theorem cell21_1754328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 2, 3].length) (baseStart_1754328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1754328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1754328 prefixEnd_1754328 := by exact prefixLift 1754328
  have htrace : WordTrace (prefixWord ++ tailWord_1754328) baseStart_1754328 baseEnd_1754328 := by
    simpa [prefixWord, tailWord_1754328, baseEnd_1754328] using wordTrace_append hprefix tailTrace_1754328
  have hstable : (prefixWord ++ tailWord_1754328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754328).length < 2 ^ (prefixWord ++ tailWord_1754328).sum := by decide
  have hdescent : baseEnd_1754328 < baseStart_1754328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754438 : List Nat := [6, 1, 1, 3, 1, 1, 3, 2, 3]
def baseStart_1754438 : Nat := 118140960795 + 1754438 * 2 ^ 59
def prefixEnd_1754438 : Nat := 4983230072969 + 3 ^ 40 * 1754438 * 2
def baseEnd_1754438 : Nat := 400386654450183105313997

theorem tailTrace_1754438 : CollatzResearch.WordTrace tailWord_1754438 prefixEnd_1754438 400386654450183105313997 := by
  unfold tailWord_1754438
  simp only [CollatzResearch.WordTrace]
  refine ⟨1999675338061819843762999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 42659740545318823333610645 1999675338061819843762999)
  ·
    refine ⟨2999513007092729765644499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1999675338061819843762999 2999513007092729765644499)
    ·
      refine ⟨4499269510639094648466749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2999513007092729765644499 4499269510639094648466749)
      ·
        refine ⟨1687226066489660493175031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4499269510639094648466749 1687226066489660493175031)
        ·
          refine ⟨2530839099734490739762547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1687226066489660493175031 2530839099734490739762547)
          ·
            refine ⟨3796258649601736109643821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2530839099734490739762547 3796258649601736109643821)
            ·
              refine ⟨1423596993600651041116433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3796258649601736109643821 1423596993600651041116433)
              ·
                refine ⟨1067697745200488280837325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1423596993600651041116433 1067697745200488280837325)
                ·
                  refine ⟨400386654450183105313997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1067697745200488280837325 400386654450183105313997)
                  ·
                    rfl

theorem cell21_1754438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_1754438 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1754438 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1754438 prefixEnd_1754438 := by exact prefixLift 1754438
  have htrace : WordTrace (prefixWord ++ tailWord_1754438) baseStart_1754438 baseEnd_1754438 := by
    simpa [prefixWord, tailWord_1754438, baseEnd_1754438] using wordTrace_append hprefix tailTrace_1754438
  have hstable : (prefixWord ++ tailWord_1754438).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754438).length < 2 ^ (prefixWord ++ tailWord_1754438).sum := by decide
  have hdescent : baseEnd_1754438 < baseStart_1754438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754457 : List Nat := [1, 2, 1, 2, 2, 2, 3, 8]
def baseStart_1754457 : Nat := 118140960795 + 1754457 * 2 ^ 59
def prefixEnd_1754457 : Nat := 4983230072969 + 3 ^ 40 * 1754457 * 2
def baseEnd_1754457 : Nat := 133463663503014431499097

theorem tailTrace_1754457 : CollatzResearch.WordTrace tailWord_1754457 prefixEnd_1754457 133463663503014431499097 := by
  unfold tailWord_1754457
  simp only [CollatzResearch.WordTrace]
  refine ⟨63990303804909401245357625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42660202536606267496905083 63990303804909401245357625)
  ·
    refine ⟨47992727853682050934018219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63990303804909401245357625 47992727853682050934018219)
    ·
      refine ⟨71989091780523076401027329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47992727853682050934018219 71989091780523076401027329)
      ·
        refine ⟨53991818835392307300770497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71989091780523076401027329 53991818835392307300770497)
        ·
          refine ⟨40493864126544230475577873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53991818835392307300770497 40493864126544230475577873)
          ·
            refine ⟨30370398094908172856683405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40493864126544230475577873 30370398094908172856683405)
            ·
              refine ⟨11388899285590564821256277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30370398094908172856683405 11388899285590564821256277)
              ·
                refine ⟨133463663503014431499097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11388899285590564821256277 133463663503014431499097)
                ·
                  rfl

theorem cell21_1754457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 8].length) (baseStart_1754457 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1754457 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1754457 prefixEnd_1754457 := by exact prefixLift 1754457
  have htrace : WordTrace (prefixWord ++ tailWord_1754457) baseStart_1754457 baseEnd_1754457 := by
    simpa [prefixWord, tailWord_1754457, baseEnd_1754457] using wordTrace_append hprefix tailTrace_1754457
  have hstable : (prefixWord ++ tailWord_1754457).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754457).length < 2 ^ (prefixWord ++ tailWord_1754457).sum := by decide
  have hdescent : baseEnd_1754457 < baseStart_1754457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754497 : List Nat := [1, 2, 4, 3, 3, 1, 2, 2, 3]
def baseStart_1754497 : Nat := 118140960795 + 1754497 * 2 ^ 59
def prefixEnd_1754497 : Nat := 4983230072969 + 3 ^ 40 * 1754497 * 2
def baseEnd_1754497 : Nat := 400400119054012113830543

theorem tailTrace_1754497 : CollatzResearch.WordTrace tailWord_1754497 prefixEnd_1754497 400400119054012113830543 := by
  unfold tailWord_1754497
  simp only [CollatzResearch.WordTrace]
  refine ⟨63991762724764488076813745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42661175149842992051209163 63991762724764488076813745)
  ·
    refine ⟨47993822043573366057610309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63991762724764488076813745 47993822043573366057610309)
    ·
      refine ⟨8998841633170006135801933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47993822043573366057610309 8998841633170006135801933)
      ·
        refine ⟨3374565612438752300925725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8998841633170006135801933 3374565612438752300925725)
        ·
          refine ⟨1265462104664532112847147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3374565612438752300925725 1265462104664532112847147)
          ·
            refine ⟨1898193156996798169270721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1265462104664532112847147 1898193156996798169270721)
            ·
              refine ⟨1423644867747598626953041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1898193156996798169270721 1423644867747598626953041)
              ·
                refine ⟨1067733650810698970214781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1423644867747598626953041 1067733650810698970214781)
                ·
                  refine ⟨400400119054012113830543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1067733650810698970214781 400400119054012113830543)
                  ·
                    rfl

theorem cell21_1754497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 2, 3].length) (baseStart_1754497 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1754497 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1754497 prefixEnd_1754497 := by exact prefixLift 1754497
  have htrace : WordTrace (prefixWord ++ tailWord_1754497) baseStart_1754497 baseEnd_1754497 := by
    simpa [prefixWord, tailWord_1754497, baseEnd_1754497] using wordTrace_append hprefix tailTrace_1754497
  have hstable : (prefixWord ++ tailWord_1754497).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754497).length < 2 ^ (prefixWord ++ tailWord_1754497).sum := by decide
  have hdescent : baseEnd_1754497 < baseStart_1754497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754553 : List Nat := [1, 2, 1, 4, 4, 2, 1, 2, 4]
def baseStart_1754553 : Nat := 118140960795 + 1754553 * 2 ^ 59
def prefixEnd_1754553 : Nat := 4983230072969 + 3 ^ 40 * 1754553 * 2
def baseEnd_1754553 : Nat := 400412899016968460897095

theorem tailTrace_1754553 : CollatzResearch.WordTrace tailWord_1754553 prefixEnd_1754553 400412899016968460897095 := by
  unfold tailWord_1754553
  simp only [CollatzResearch.WordTrace]
  refine ⟨63993805212561609640852313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42662536808374406427234875 63993805212561609640852313)
  ·
    refine ⟨47995353909421207230639235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63993805212561609640852313 47995353909421207230639235)
    ·
      refine ⟨71993030864131810845958853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47995353909421207230639235 71993030864131810845958853)
      ·
        refine ⟨13498693287024714533617285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71993030864131810845958853 13498693287024714533617285)
        ·
          refine ⟨2531004991317133975053241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13498693287024714533617285 2531004991317133975053241)
          ·
            refine ⟨1898253743487850481289931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2531004991317133975053241 1898253743487850481289931)
            ·
              refine ⟨2847380615231775721934897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1898253743487850481289931 2847380615231775721934897)
              ·
                refine ⟨2135535461423831791451173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2847380615231775721934897 2135535461423831791451173)
                ·
                  refine ⟨400412899016968460897095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2135535461423831791451173 400412899016968460897095)
                  ·
                    rfl

theorem cell21_1754553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 2, 4].length) (baseStart_1754553 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1754553 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1754553 prefixEnd_1754553 := by exact prefixLift 1754553
  have htrace : WordTrace (prefixWord ++ tailWord_1754553) baseStart_1754553 baseEnd_1754553 := by
    simpa [prefixWord, tailWord_1754553, baseEnd_1754553] using wordTrace_append hprefix tailTrace_1754553
  have hstable : (prefixWord ++ tailWord_1754553).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754553).length < 2 ^ (prefixWord ++ tailWord_1754553).sum := by decide
  have hdescent : baseEnd_1754553 < baseStart_1754553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754595 : List Nat := [1, 1, 1, 6, 2, 1, 1, 2, 6]
def baseStart_1754595 : Nat := 118140960795 + 1754595 * 2 ^ 59
def prefixEnd_1754595 : Nat := 4983230072969 + 3 ^ 40 * 1754595 * 2
def baseEnd_1754595 : Nat := 400422483989185721197009

theorem tailTrace_1754595 : CollatzResearch.WordTrace tailWord_1754595 prefixEnd_1754595 400422483989185721197009 := by
  unfold tailWord_1754595
  simp only [CollatzResearch.WordTrace]
  refine ⟨63995337078409450813881239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42663558052272967209254159 63995337078409450813881239)
  ·
    refine ⟨95993005617614176220821859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63995337078409450813881239 95993005617614176220821859)
    ·
      refine ⟨143989508426421264331232789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95993005617614176220821859 143989508426421264331232789)
      ·
        refine ⟨6749508207488496765526537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 143989508426421264331232789 6749508207488496765526537)
        ·
          refine ⟨5062131155616372574144903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6749508207488496765526537 5062131155616372574144903)
          ·
            refine ⟨7593196733424558861217355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5062131155616372574144903 7593196733424558861217355)
            ·
              refine ⟨11389795100136838291826033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7593196733424558861217355 11389795100136838291826033)
              ·
                refine ⟨8542346325102628718869525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11389795100136838291826033 8542346325102628718869525)
                ·
                  refine ⟨400422483989185721197009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8542346325102628718869525 400422483989185721197009)
                  ·
                    rfl

theorem cell21_1754595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 6].length) (baseStart_1754595 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1754595 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1754595 prefixEnd_1754595 := by exact prefixLift 1754595
  have htrace : WordTrace (prefixWord ++ tailWord_1754595) baseStart_1754595 baseEnd_1754595 := by
    simpa [prefixWord, tailWord_1754595, baseEnd_1754595] using wordTrace_append hprefix tailTrace_1754595
  have hstable : (prefixWord ++ tailWord_1754595).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754595).length < 2 ^ (prefixWord ++ tailWord_1754595).sum := by decide
  have hdescent : baseEnd_1754595 < baseStart_1754595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754609 : List Nat := [1, 2, 2, 2, 3, 2, 9]
def baseStart_1754609 : Nat := 118140960795 + 1754609 * 2 ^ 59
def prefixEnd_1754609 : Nat := 4983230072969 + 3 ^ 40 * 1754609 * 2
def baseEnd_1754609 : Nat := 44491742108880534218183

theorem tailTrace_1754609 : CollatzResearch.WordTrace tailWord_1754609 prefixEnd_1754609 44491742108880534218183 := by
  unfold tailWord_1754609
  simp only [CollatzResearch.WordTrace]
  refine ⟨63995847700358731204890881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42663898466905820803260587 63995847700358731204890881)
  ·
    refine ⟨47996885775269048403668161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63995847700358731204890881 47996885775269048403668161)
    ·
      refine ⟨35997664331451786302751121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47996885775269048403668161 35997664331451786302751121)
      ·
        refine ⟨26998248248588839727063341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35997664331451786302751121 26998248248588839727063341)
        ·
          refine ⟨10124343093220814897648753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26998248248588839727063341 10124343093220814897648753)
          ·
            refine ⟨7593257319915611173236565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10124343093220814897648753 7593257319915611173236565)
            ·
              refine ⟨44491742108880534218183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7593257319915611173236565 44491742108880534218183)
              ·
                rfl

theorem cell21_1754609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 9].length) (baseStart_1754609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1754609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1754609 prefixEnd_1754609 := by exact prefixLift 1754609
  have htrace : WordTrace (prefixWord ++ tailWord_1754609) baseStart_1754609 baseEnd_1754609 := by
    simpa [prefixWord, tailWord_1754609, baseEnd_1754609] using wordTrace_append hprefix tailTrace_1754609
  have hstable : (prefixWord ++ tailWord_1754609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754609).length < 2 ^ (prefixWord ++ tailWord_1754609).sum := by decide
  have hdescent : baseEnd_1754609 < baseStart_1754609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754930 : List Nat := [3, 2, 1, 1, 3, 2, 4, 5]
def baseStart_1754930 : Nat := 118140960795 + 1754930 * 2 ^ 59
def prefixEnd_1754930 : Nat := 4983230072969 + 3 ^ 40 * 1754930 * 2
def baseEnd_1754930 : Nat := 133499645184433194370997

theorem tailTrace_1754930 : CollatzResearch.WordTrace tailWord_1754930 prefixEnd_1754930 133499645184433194370997 := by
  unfold tailWord_1754930
  simp only [CollatzResearch.WordTrace]
  refine ⟨16001888883048950756831561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42671703688130535351550829 16001888883048950756831561)
  ·
    refine ⟨12001416662286713067623671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16001888883048950756831561 12001416662286713067623671)
    ·
      refine ⟨18002124993430069601435507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12001416662286713067623671 18002124993430069601435507)
      ·
        refine ⟨27003187490145104402153261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18002124993430069601435507 27003187490145104402153261)
        ·
          refine ⟨10126195308804414150807473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27003187490145104402153261 10126195308804414150807473)
          ·
            refine ⟨7594646481603310613105605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10126195308804414150807473 7594646481603310613105605)
            ·
              refine ⟨1423996215300620739957301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7594646481603310613105605 1423996215300620739957301)
              ·
                refine ⟨133499645184433194370997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1423996215300620739957301 133499645184433194370997)
                ·
                  rfl

theorem cell21_1754930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 5].length) (baseStart_1754930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1754930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1754930 prefixEnd_1754930 := by exact prefixLift 1754930
  have htrace : WordTrace (prefixWord ++ tailWord_1754930) baseStart_1754930 baseEnd_1754930 := by
    simpa [prefixWord, tailWord_1754930, baseEnd_1754930] using wordTrace_append hprefix tailTrace_1754930
  have hstable : (prefixWord ++ tailWord_1754930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754930).length < 2 ^ (prefixWord ++ tailWord_1754930).sum := by decide
  have hdescent : baseEnd_1754930 < baseStart_1754930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754961 : List Nat := [1, 2, 2, 1, 5, 3, 1, 1, 5]
def baseStart_1754961 : Nat := 118140960795 + 1754961 * 2 ^ 59
def prefixEnd_1754961 : Nat := 4983230072969 + 3 ^ 40 * 1754961 * 2
def baseEnd_1754961 : Nat := 400506010175650418096261

theorem tailTrace_1754961 : CollatzResearch.WordTrace tailWord_1754961 prefixEnd_1754961 400506010175650418096261 := by
  unfold tailWord_1754961
  simp only [CollatzResearch.WordTrace]
  refine ⟨64008686195083495321704737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42672457463388996881136491 64008686195083495321704737)
  ·
    refine ⟨48006514646312621491278553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64008686195083495321704737 48006514646312621491278553)
    ·
      refine ⟨36004885984734466118458915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48006514646312621491278553 36004885984734466118458915)
      ·
        refine ⟨54007328977101699177688373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36004885984734466118458915 54007328977101699177688373)
        ·
          refine ⟨5063187091603284297908285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54007328977101699177688373 5063187091603284297908285)
          ·
            refine ⟨1898695159351231611715607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5063187091603284297908285 1898695159351231611715607)
            ·
              refine ⟨2848042739026847417573411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1898695159351231611715607 2848042739026847417573411)
              ·
                refine ⟨4272064108540271126360117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2848042739026847417573411 4272064108540271126360117)
                ·
                  refine ⟨400506010175650418096261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4272064108540271126360117 400506010175650418096261)
                  ·
                    rfl

theorem cell21_1754961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 5].length) (baseStart_1754961 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1754961 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1754961 prefixEnd_1754961 := by exact prefixLift 1754961
  have htrace : WordTrace (prefixWord ++ tailWord_1754961) baseStart_1754961 baseEnd_1754961 := by
    simpa [prefixWord, tailWord_1754961, baseEnd_1754961] using wordTrace_append hprefix tailTrace_1754961
  have hstable : (prefixWord ++ tailWord_1754961).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754961).length < 2 ^ (prefixWord ++ tailWord_1754961).sum := by decide
  have hdescent : baseEnd_1754961 < baseStart_1754961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754975 : List Nat := [1, 1, 2, 3, 1, 5, 1, 3, 4]
def baseStart_1754975 : Nat := 118140960795 + 1754975 * 2 ^ 59
def prefixEnd_1754975 : Nat := 4983230072969 + 3 ^ 40 * 1754975 * 2
def baseEnd_1754975 : Nat := 400509205166389504862899

theorem tailTrace_1754975 : CollatzResearch.WordTrace tailWord_1754975 prefixEnd_1754975 400509205166389504862899 := by
  unfold tailWord_1754975
  simp only [CollatzResearch.WordTrace]
  refine ⟨64009196817032775712714379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42672797878021850475142919 64009196817032775712714379)
  ·
    refine ⟨96013795225549163569071569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64009196817032775712714379 96013795225549163569071569)
    ·
      refine ⟨72010346419161872676803677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96013795225549163569071569 72010346419161872676803677)
      ·
        refine ⟨27003879907185702253801379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72010346419161872676803677 27003879907185702253801379)
        ·
          refine ⟨40505819860778553380702069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27003879907185702253801379 40505819860778553380702069)
          ·
            refine ⟨3797420611947989379440819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40505819860778553380702069 3797420611947989379440819)
            ·
              refine ⟨5696130917921984069161229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3797420611947989379440819 5696130917921984069161229)
              ·
                refine ⟨2136049094220744025935461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5696130917921984069161229 2136049094220744025935461)
                ·
                  refine ⟨400509205166389504862899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2136049094220744025935461 400509205166389504862899)
                  ·
                    rfl

theorem cell21_1754975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 3, 4].length) (baseStart_1754975 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1754975 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1754975 prefixEnd_1754975 := by exact prefixLift 1754975
  have htrace : WordTrace (prefixWord ++ tailWord_1754975) baseStart_1754975 baseEnd_1754975 := by
    simpa [prefixWord, tailWord_1754975, baseEnd_1754975] using wordTrace_append hprefix tailTrace_1754975
  have hstable : (prefixWord ++ tailWord_1754975).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754975).length < 2 ^ (prefixWord ++ tailWord_1754975).sum := by decide
  have hdescent : baseEnd_1754975 < baseStart_1754975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1754989 : List Nat := [1, 5, 1, 1, 1, 1, 4, 7]
def baseStart_1754989 : Nat := 118140960795 + 1754989 * 2 ^ 59
def prefixEnd_1754989 : Nat := 4983230072969 + 3 ^ 40 * 1754989 * 2
def baseEnd_1754989 : Nat := 133504133385709530543179

theorem tailTrace_1754989 : CollatzResearch.WordTrace tailWord_1754989 prefixEnd_1754989 133504133385709530543179 := by
  unfold tailWord_1754989
  simp only [CollatzResearch.WordTrace]
  refine ⟨64009707438982056103724021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42673138292654704069149347 64009707438982056103724021)
  ·
    refine ⟨6000910072404567759724127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64009707438982056103724021 6000910072404567759724127)
    ·
      refine ⟨9001365108606851639586191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6000910072404567759724127 9001365108606851639586191)
      ·
        refine ⟨13502047662910277459379287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9001365108606851639586191 13502047662910277459379287)
        ·
          refine ⟨20253071494365416189068931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13502047662910277459379287 20253071494365416189068931)
          ·
            refine ⟨30379607241548124283603397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20253071494365416189068931 30379607241548124283603397)
            ·
              refine ⟨5696176357790273303175637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30379607241548124283603397 5696176357790273303175637)
              ·
                refine ⟨133504133385709530543179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5696176357790273303175637 133504133385709530543179)
                ·
                  rfl

theorem cell21_1754989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 7].length) (baseStart_1754989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1754989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1754989 prefixEnd_1754989 := by exact prefixLift 1754989
  have htrace : WordTrace (prefixWord ++ tailWord_1754989) baseStart_1754989 baseEnd_1754989 := by
    simpa [prefixWord, tailWord_1754989, baseEnd_1754989] using wordTrace_append hprefix tailTrace_1754989
  have hstable : (prefixWord ++ tailWord_1754989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1754989).length < 2 ^ (prefixWord ++ tailWord_1754989).sum := by decide
  have hdescent : baseEnd_1754989 < baseStart_1754989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1754989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755006 : List Nat := [4, 2, 3, 1, 1, 10]
def baseStart_1755006 : Nat := 118140960795 + 1755006 * 2 ^ 59
def prefixEnd_1755006 : Nat := 4983230072969 + 3 ^ 40 * 1755006 * 2
def baseEnd_1755006 : Nat := 14833936288471864438747

theorem tailTrace_1755006 : CollatzResearch.WordTrace tailWord_1755006 prefixEnd_1755006 14833936288471864438747 := by
  unfold tailWord_1755006
  simp only [CollatzResearch.WordTrace]
  refine ⟨8001290934990058500886609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42673551653280312004728581 8001290934990058500886609)
  ·
    refine ⟨6000968201242543875664957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8001290934990058500886609 6000968201242543875664957)
    ·
      refine ⟨2250363075465953953374359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6000968201242543875664957 2250363075465953953374359)
      ·
        refine ⟨3375544613198930930061539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2250363075465953953374359 3375544613198930930061539)
        ·
          refine ⟨5063316919798396395092309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3375544613198930930061539 5063316919798396395092309)
          ·
            refine ⟨14833936288471864438747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5063316919798396395092309 14833936288471864438747)
            ·
              rfl

theorem cell21_1755006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 10].length) (baseStart_1755006 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1755006 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1755006 prefixEnd_1755006 := by exact prefixLift 1755006
  have htrace : WordTrace (prefixWord ++ tailWord_1755006) baseStart_1755006 baseEnd_1755006 := by
    simpa [prefixWord, tailWord_1755006, baseEnd_1755006] using wordTrace_append hprefix tailTrace_1755006
  have hstable : (prefixWord ++ tailWord_1755006).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755006).length < 2 ^ (prefixWord ++ tailWord_1755006).sum := by decide
  have hdescent : baseEnd_1755006 < baseStart_1755006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755009 : List Nat := [1, 2, 4, 4, 1, 1, 2, 2, 4]
def baseStart_1755009 : Nat := 118140960795 + 1755009 * 2 ^ 59
def prefixEnd_1755009 : Nat := 4983230072969 + 3 ^ 40 * 1755009 * 2
def baseEnd_1755009 : Nat := 400516964429613001296163

theorem tailTrace_1755009 : CollatzResearch.WordTrace tailWord_1755009 prefixEnd_1755009 400516964429613001296163 := by
  unfold tailWord_1755009
  simp only [CollatzResearch.WordTrace]
  refine ⟨64010436898909599519452081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42673624599273066346301387 64010436898909599519452081)
  ·
    refine ⟨48007827674182199639589061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64010436898909599519452081 48007827674182199639589061)
    ·
      refine ⟨9001467688909162432422949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48007827674182199639589061 9001467688909162432422949)
      ·
        refine ⟨1687775191670467956079303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9001467688909162432422949 1687775191670467956079303)
        ·
          refine ⟨2531662787505701934118955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1687775191670467956079303 2531662787505701934118955)
          ·
            refine ⟨3797494181258552901178433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2531662787505701934118955 3797494181258552901178433)
            ·
              refine ⟨2848120635943914675883825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3797494181258552901178433 2848120635943914675883825)
              ·
                refine ⟨2136090476957936006912869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2848120635943914675883825 2136090476957936006912869)
                ·
                  refine ⟨400516964429613001296163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2136090476957936006912869 400516964429613001296163)
                  ·
                    rfl

theorem cell21_1755009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 2, 4].length) (baseStart_1755009 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1755009 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1755009 prefixEnd_1755009 := by exact prefixLift 1755009
  have htrace : WordTrace (prefixWord ++ tailWord_1755009) baseStart_1755009 baseEnd_1755009 := by
    simpa [prefixWord, tailWord_1755009, baseEnd_1755009] using wordTrace_append hprefix tailTrace_1755009
  have hstable : (prefixWord ++ tailWord_1755009).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755009).length < 2 ^ (prefixWord ++ tailWord_1755009).sum := by decide
  have hdescent : baseEnd_1755009 < baseStart_1755009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755068 : List Nat := [2, 2, 2, 5, 1, 1, 1, 1, 6]
def baseStart_1755068 : Nat := 118140960795 + 1755068 * 2 ^ 59
def prefixEnd_1755068 : Nat := 4983230072969 + 3 ^ 40 * 1755068 * 2
def baseEnd_1755068 : Nat := 400530429033442009812709

theorem tailTrace_1755068 : CollatzResearch.WordTrace tailWord_1755068 prefixEnd_1755068 400530429033442009812709 := by
  unfold tailWord_1755068
  simp only [CollatzResearch.WordTrace]
  refine ⟨32006294402847926297924929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42675059203797235063899905 32006294402847926297924929)
  ·
    refine ⟨24004720802135944723443697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32006294402847926297924929 24004720802135944723443697)
    ·
      refine ⟨18003540601601958542582773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24004720802135944723443697 18003540601601958542582773)
      ·
        refine ⟨1687831931400183613367135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18003540601601958542582773 1687831931400183613367135)
        ·
          refine ⟨2531747897100275420050703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1687831931400183613367135 2531747897100275420050703)
          ·
            refine ⟨3797621845650413130076055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2531747897100275420050703 3797621845650413130076055)
            ·
              refine ⟨5696432768475619695114083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3797621845650413130076055 5696432768475619695114083)
              ·
                refine ⟨8544649152713429542671125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5696432768475619695114083 8544649152713429542671125)
                ·
                  refine ⟨400530429033442009812709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8544649152713429542671125 400530429033442009812709)
                  ·
                    rfl

theorem cell21_1755068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 6].length) (baseStart_1755068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1755068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1755068 prefixEnd_1755068 := by exact prefixLift 1755068
  have htrace : WordTrace (prefixWord ++ tailWord_1755068) baseStart_1755068 baseEnd_1755068 := by
    simpa [prefixWord, tailWord_1755068, baseEnd_1755068] using wordTrace_append hprefix tailTrace_1755068
  have hstable : (prefixWord ++ tailWord_1755068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755068).length < 2 ^ (prefixWord ++ tailWord_1755068).sum := by decide
  have hdescent : baseEnd_1755068 < baseStart_1755068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755141 : List Nat := [1, 3, 1, 1, 2, 5, 2, 6]
def baseStart_1755141 : Nat := 118140960795 + 1755141 * 2 ^ 59
def prefixEnd_1755141 : Nat := 4983230072969 + 3 ^ 40 * 1755141 * 2
def baseEnd_1755141 : Nat := 133515696209336701698631

theorem tailTrace_1755141 : CollatzResearch.WordTrace tailWord_1755141 prefixEnd_1755141 133515696209336701698631 := by
  unfold tailWord_1755141
  simp only [CollatzResearch.WordTrace]
  refine ⟨64015251334431386063257277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42676834222954257375504851 64015251334431386063257277)
  ·
    refine ⟨24005719250411769773721479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64015251334431386063257277 24005719250411769773721479)
    ·
      refine ⟨36008578875617654660582219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24005719250411769773721479 36008578875617654660582219)
      ·
        refine ⟨54012868313426481990873329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36008578875617654660582219 54012868313426481990873329)
        ·
          refine ⟨40509651235069861493154997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54012868313426481990873329 40509651235069861493154997)
          ·
            refine ⟨3797779803287799514983281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40509651235069861493154997 3797779803287799514983281)
            ·
              refine ⟨2848334852465849636237461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3797779803287799514983281 2848334852465849636237461)
              ·
                refine ⟨133515696209336701698631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2848334852465849636237461 133515696209336701698631)
                ·
                  rfl

theorem cell21_1755141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 6].length) (baseStart_1755141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1755141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1755141 prefixEnd_1755141 := by exact prefixLift 1755141
  have htrace : WordTrace (prefixWord ++ tailWord_1755141) baseStart_1755141 baseEnd_1755141 := by
    simpa [prefixWord, tailWord_1755141, baseEnd_1755141] using wordTrace_append hprefix tailTrace_1755141
  have hstable : (prefixWord ++ tailWord_1755141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755141).length < 2 ^ (prefixWord ++ tailWord_1755141).sum := by decide
  have hdescent : baseEnd_1755141 < baseStart_1755141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755155 : List Nat := [1, 1, 1, 2, 1, 4, 2, 4, 5]
def baseStart_1755155 : Nat := 118140960795 + 1755155 * 2 ^ 59
def prefixEnd_1755155 : Nat := 4983230072969 + 3 ^ 40 * 1755155 * 2
def baseEnd_1755155 : Nat := 400550283618749191862531

theorem tailTrace_1755155 : CollatzResearch.WordTrace tailWord_1755155 prefixEnd_1755155 400550283618749191862531 := by
  unfold tailWord_1755155
  simp only [CollatzResearch.WordTrace]
  refine ⟨64015761956380666454266919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42677174637587110969511279 64015761956380666454266919)
  ·
    refine ⟨96023642934570999681400379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64015761956380666454266919 96023642934570999681400379)
    ·
      refine ⟨144035464401856499522100569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96023642934570999681400379 144035464401856499522100569)
      ·
        refine ⟨108026598301392374641575427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144035464401856499522100569 108026598301392374641575427)
        ·
          refine ⟨162039897452088561962363141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108026598301392374641575427 162039897452088561962363141)
          ·
            refine ⟨30382480772266605367943089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 162039897452088561962363141 30382480772266605367943089)
            ·
              refine ⟨22786860579199954025957317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30382480772266605367943089 22786860579199954025957317)
              ·
                refine ⟨4272536358599991379866997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22786860579199954025957317 4272536358599991379866997)
                ·
                  refine ⟨400550283618749191862531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4272536358599991379866997 400550283618749191862531)
                  ·
                    rfl

theorem cell21_1755155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 5].length) (baseStart_1755155 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1755155 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1755155 prefixEnd_1755155 := by exact prefixLift 1755155
  have htrace : WordTrace (prefixWord ++ tailWord_1755155) baseStart_1755155 baseEnd_1755155 := by
    simpa [prefixWord, tailWord_1755155, baseEnd_1755155] using wordTrace_append hprefix tailTrace_1755155
  have hstable : (prefixWord ++ tailWord_1755155).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755155).length < 2 ^ (prefixWord ++ tailWord_1755155).sum := by decide
  have hdescent : baseEnd_1755155 < baseStart_1755155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755234 : List Nat := [3, 3, 2, 2, 2, 1, 8]
def baseStart_1755234 : Nat := 118140960795 + 1755234 * 2 ^ 59
def prefixEnd_1755234 : Nat := 4983230072969 + 3 ^ 40 * 1755234 * 2
def baseEnd_1755234 : Nat := 44507590277229178893967

theorem tailTrace_1755234 : CollatzResearch.WordTrace tailWord_1755234 prefixEnd_1755234 44507590277229178893967 := by
  unfold tailWord_1755234
  simp only [CollatzResearch.WordTrace]
  refine ⟨16004660830773615736598189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42679095548729641964261837 16004660830773615736598189)
  ·
    refine ⟨6001747811540105901224321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16004660830773615736598189 6001747811540105901224321)
    ·
      refine ⟨4501310858655079425918241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6001747811540105901224321 4501310858655079425918241)
      ·
        refine ⟨3375983143991309569438681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4501310858655079425918241 3375983143991309569438681)
        ·
          refine ⟨2531987357993482177079011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3375983143991309569438681 2531987357993482177079011)
          ·
            refine ⟨3797981036990223265618517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2531987357993482177079011 3797981036990223265618517)
            ·
              refine ⟨44507590277229178893967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3797981036990223265618517 44507590277229178893967)
              ·
                rfl

theorem cell21_1755234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 8].length) (baseStart_1755234 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1755234 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1755234 prefixEnd_1755234 := by exact prefixLift 1755234
  have htrace : WordTrace (prefixWord ++ tailWord_1755234) baseStart_1755234 baseEnd_1755234 := by
    simpa [prefixWord, tailWord_1755234, baseEnd_1755234] using wordTrace_append hprefix tailTrace_1755234
  have hstable : (prefixWord ++ tailWord_1755234).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755234).length < 2 ^ (prefixWord ++ tailWord_1755234).sum := by decide
  have hdescent : baseEnd_1755234 < baseStart_1755234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755248 : List Nat := [2, 1, 1, 1, 5, 3, 2, 1, 5]
def baseStart_1755248 : Nat := 118140960795 + 1755248 * 2 ^ 59
def prefixEnd_1755248 : Nat := 4983230072969 + 3 ^ 40 * 1755248 * 2
def baseEnd_1755248 : Nat := 400571507485801696812341

theorem tailTrace_1755248 : CollatzResearch.WordTrace tailWord_1755248 prefixEnd_1755248 400571507485801696812341 := by
  unfold tailWord_1755248
  simp only [CollatzResearch.WordTrace]
  refine ⟨32009576972521871668701199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42679435963362495558268265 32009576972521871668701199)
  ·
    refine ⟨48014365458782807503051799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32009576972521871668701199 48014365458782807503051799)
    ·
      refine ⟨72021548188174211254577699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48014365458782807503051799 72021548188174211254577699)
      ·
        refine ⟨108032322282261316881866549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72021548188174211254577699 108032322282261316881866549)
        ·
          refine ⟨10128030213961998457674989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108032322282261316881866549 10128030213961998457674989)
          ·
            refine ⟨3798011330235749421628121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10128030213961998457674989 3798011330235749421628121)
            ·
              refine ⟨2848508497676812066221091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3798011330235749421628121 2848508497676812066221091)
              ·
                refine ⟨4272762746515218099331637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2848508497676812066221091 4272762746515218099331637)
                ·
                  refine ⟨400571507485801696812341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4272762746515218099331637 400571507485801696812341)
                  ·
                    rfl

theorem cell21_1755248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 5].length) (baseStart_1755248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1755248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1755248 prefixEnd_1755248 := by exact prefixLift 1755248
  have htrace : WordTrace (prefixWord ++ tailWord_1755248) baseStart_1755248 baseEnd_1755248 := by
    simpa [prefixWord, tailWord_1755248, baseEnd_1755248] using wordTrace_append hprefix tailTrace_1755248
  have hstable : (prefixWord ++ tailWord_1755248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755248).length < 2 ^ (prefixWord ++ tailWord_1755248).sum := by decide
  have hdescent : baseEnd_1755248 < baseStart_1755248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
