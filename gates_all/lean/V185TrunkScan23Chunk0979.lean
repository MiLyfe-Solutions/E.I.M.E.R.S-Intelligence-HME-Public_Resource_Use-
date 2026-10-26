import V185TrunkScan23Chunk0978

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5795553 : List Nat := [1, 2, 3, 1, 5, 1, 1, 2, 3, 4]
def baseStart_5795553 : Nat := 118140960795 + 5795553 * 2 ^ 59
def prefixEnd_5795553 : Nat := 4983230072969 + 3 ^ 40 * 5795553 * 2
def baseEnd_5795553 : Nat := 991968115868956201978081

theorem tailTrace_5795553 : CollatzResearch.WordTrace tailWord_5795553 prefixEnd_5795553 991968115868956201978081 := by
  unfold tailWord_5795553
  simp only [CollatzResearch.WordTrace]
  refine ⟨211381183572708757495375313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140920789048472504996916875 211381183572708757495375313)
  ·
    refine ⟨158535887679531568121531485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211381183572708757495375313 158535887679531568121531485)
    ·
      refine ⟨59450957879824338045574307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158535887679531568121531485 59450957879824338045574307)
      ·
        refine ⟨89176436819736507068361461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59450957879824338045574307 89176436819736507068361461)
        ·
          refine ⟨8360290951850297537658887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89176436819736507068361461 8360290951850297537658887)
          ·
            refine ⟨12540436427775446306488331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8360290951850297537658887 12540436427775446306488331)
            ·
              refine ⟨18810654641663169459732497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12540436427775446306488331 18810654641663169459732497)
              ·
                refine ⟨14107990981247377094799373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18810654641663169459732497 14107990981247377094799373)
                ·
                  refine ⟨5290496617967766410549765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14107990981247377094799373 5290496617967766410549765)
                  ·
                    refine ⟨991968115868956201978081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5290496617967766410549765 991968115868956201978081)
                    ·
                      rfl

theorem cell23_5795553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 3, 4].length) (baseStart_5795553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5795553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5795553 prefixEnd_5795553 := by exact prefixLift 5795553
  have htrace : WordTrace (prefixWord ++ tailWord_5795553) baseStart_5795553 baseEnd_5795553 := by
    simpa [prefixWord, tailWord_5795553, baseEnd_5795553] using wordTrace_append hprefix tailTrace_5795553
  have hstable : (prefixWord ++ tailWord_5795553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5795553).length < 2 ^ (prefixWord ++ tailWord_5795553).sum := by decide
  have hdescent : baseEnd_5795553 < baseStart_5795553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5795553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5795570 : List Nat := [3, 2, 1, 3, 1, 1, 4, 3, 1, 4]
def baseStart_5795570 : Nat := 118140960795 + 5795570 * 2 ^ 59
def prefixEnd_5795570 : Nat := 4983230072969 + 3 ^ 40 * 5795570 * 2
def baseEnd_5795570 : Nat := 991971025592665013140555

theorem tailTrace_5795570 : CollatzResearch.WordTrace tailWord_5795570 prefixEnd_5795570 991971025592665013140555 := by
  unfold tailWord_5795570
  simp only [CollatzResearch.WordTrace]
  refine ⟨52845450903411792349686041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140921202409098112932496109 52845450903411792349686041)
  ·
    refine ⟨39634088177558844262264531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52845450903411792349686041 39634088177558844262264531)
    ·
      refine ⟨59451132266338266393396797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39634088177558844262264531 59451132266338266393396797)
      ·
        refine ⟨22294174599876849897523799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59451132266338266393396797 22294174599876849897523799)
        ·
          refine ⟨33441261899815274846285699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22294174599876849897523799 33441261899815274846285699)
          ·
            refine ⟨50161892849722912269428549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33441261899815274846285699 50161892849722912269428549)
            ·
              refine ⟨9405354909323046050517853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50161892849722912269428549 9405354909323046050517853)
              ·
                refine ⟨3527008090996142268944195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9405354909323046050517853 3527008090996142268944195)
                ·
                  refine ⟨5290512136494213403416293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3527008090996142268944195 5290512136494213403416293)
                  ·
                    refine ⟨991971025592665013140555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5290512136494213403416293 991971025592665013140555)
                    ·
                      rfl

theorem cell23_5795570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 3, 1, 4].length) (baseStart_5795570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5795570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5795570 prefixEnd_5795570 := by exact prefixLift 5795570
  have htrace : WordTrace (prefixWord ++ tailWord_5795570) baseStart_5795570 baseEnd_5795570 := by
    simpa [prefixWord, tailWord_5795570, baseEnd_5795570] using wordTrace_append hprefix tailTrace_5795570
  have hstable : (prefixWord ++ tailWord_5795570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5795570).length < 2 ^ (prefixWord ++ tailWord_5795570).sum := by decide
  have hdescent : baseEnd_5795570 < baseStart_5795570 := by decide
  rcases family_descends (prefixWord ++ tailWord_5795570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5795579 : List Nat := [1, 1, 1, 1, 1, 3, 1, 4, 5, 5]
def baseStart_5795579 : Nat := 118140960795 + 5795579 * 2 ^ 59
def prefixEnd_5795579 : Nat := 4983230072969 + 3 ^ 40 * 5795579 * 2
def baseEnd_5795579 : Nat := 991972566034628501403041

theorem tailTrace_5795579 : CollatzResearch.WordTrace tailWord_5795579 prefixEnd_5795579 991972566034628501403041 := by
  unfold tailWord_5795579
  simp only [CollatzResearch.WordTrace]
  refine ⟨211382131870614563935821791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140921421247076375957214527 211382131870614563935821791)
  ·
    refine ⟨317073197805921845903732687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211382131870614563935821791 317073197805921845903732687)
    ·
      refine ⟨475609796708882768855599031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317073197805921845903732687 475609796708882768855599031)
      ·
        refine ⟨713414695063324153283398547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475609796708882768855599031 713414695063324153283398547)
        ·
          refine ⟨1070122042594986229925097821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 713414695063324153283398547 1070122042594986229925097821)
          ·
            refine ⟨401295765973119836221911683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1070122042594986229925097821 401295765973119836221911683)
            ·
              refine ⟨601943648959679754332867525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 401295765973119836221911683 601943648959679754332867525)
              ·
                refine ⟨112864434179939953937412661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 601943648959679754332867525 112864434179939953937412661)
                ·
                  refine ⟨10581040704369370681632437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 112864434179939953937412661 10581040704369370681632437)
                  ·
                    refine ⟨991972566034628501403041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10581040704369370681632437 991972566034628501403041)
                    ·
                      rfl

theorem cell23_5795579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 5, 5].length) (baseStart_5795579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5795579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5795579 prefixEnd_5795579 := by exact prefixLift 5795579
  have htrace : WordTrace (prefixWord ++ tailWord_5795579) baseStart_5795579 baseEnd_5795579 := by
    simpa [prefixWord, tailWord_5795579, baseEnd_5795579] using wordTrace_append hprefix tailTrace_5795579
  have hstable : (prefixWord ++ tailWord_5795579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5795579).length < 2 ^ (prefixWord ++ tailWord_5795579).sum := by decide
  have hdescent : baseEnd_5795579 < baseStart_5795579 := by decide
  rcases family_descends (prefixWord ++ tailWord_5795579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5795586 : List Nat := [3, 4, 1, 1, 1, 1, 1, 1, 1, 1, 8]
def baseStart_5795586 : Nat := 118140960795 + 5795586 * 2 ^ 59
def prefixEnd_5795586 : Nat := 4983230072969 + 3 ^ 40 * 5795586 * 2
def baseEnd_5795586 : Nat := 2975921292468466976821591

theorem tailTrace_5795586 : CollatzResearch.WordTrace tailWord_5795586 prefixEnd_5795586 2975921292468466976821591 := by
  unfold tailWord_5795586
  simp only [CollatzResearch.WordTrace]
  refine ⟨52845596795397301032831653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140921591454392802754217741 52845596795397301032831653)
  ·
    refine ⟨9908549399136993943655935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52845596795397301032831653 9908549399136993943655935)
    ·
      refine ⟨14862824098705490915483903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9908549399136993943655935 14862824098705490915483903)
      ·
        refine ⟨22294236148058236373225855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14862824098705490915483903 22294236148058236373225855)
        ·
          refine ⟨33441354222087354559838783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22294236148058236373225855 33441354222087354559838783)
          ·
            refine ⟨50162031333131031839758175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33441354222087354559838783 50162031333131031839758175)
            ·
              refine ⟨75243046999696547759637263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50162031333131031839758175 75243046999696547759637263)
              ·
                refine ⟨112864570499544821639455895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75243046999696547759637263 112864570499544821639455895)
                ·
                  refine ⟨169296855749317232459183843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112864570499544821639455895 169296855749317232459183843)
                  ·
                    refine ⟨253945283623975848688775765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 169296855749317232459183843 253945283623975848688775765)
                    ·
                      refine ⟨2975921292468466976821591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 253945283623975848688775765 2975921292468466976821591)
                      ·
                        rfl

theorem cell23_5795586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_5795586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5795586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5795586 prefixEnd_5795586 := by exact prefixLift 5795586
  have htrace : WordTrace (prefixWord ++ tailWord_5795586) baseStart_5795586 baseEnd_5795586 := by
    simpa [prefixWord, tailWord_5795586, baseEnd_5795586] using wordTrace_append hprefix tailTrace_5795586
  have hstable : (prefixWord ++ tailWord_5795586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5795586).length < 2 ^ (prefixWord ++ tailWord_5795586).sum := by decide
  have hdescent : baseEnd_5795586 < baseStart_5795586 := by decide
  rcases family_descends (prefixWord ++ tailWord_5795586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5795599 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 2, 5, 4]
def baseStart_5795599 : Nat := 118140960795 + 5795599 * 2 ^ 59
def prefixEnd_5795599 : Nat := 4983230072969 + 3 ^ 40 * 5795599 * 2
def baseEnd_5795599 : Nat := 2975927967716975425959031

theorem tailTrace_5795599 : CollatzResearch.WordTrace tailWord_5795599 prefixEnd_5795599 2975927967716975425959031 := by
  unfold tailWord_5795599
  simp only [CollatzResearch.WordTrace]
  refine ⟨211382861330542107351549851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140921907553694738234366567 211382861330542107351549851)
  ·
    refine ⟨317074291995813161027324777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211382861330542107351549851 317074291995813161027324777)
    ·
      refine ⟨237805718996859870770493583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317074291995813161027324777 237805718996859870770493583)
      ·
        refine ⟨356708578495289806155740375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237805718996859870770493583 356708578495289806155740375)
        ·
          refine ⟨535062867742934709233610563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356708578495289806155740375 535062867742934709233610563)
          ·
            refine ⟨802594301614402063850415845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 535062867742934709233610563 802594301614402063850415845)
            ·
              refine ⟨150486431552700386971952971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 802594301614402063850415845 150486431552700386971952971)
              ·
                refine ⟨225729647329050580457929457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150486431552700386971952971 225729647329050580457929457)
                ·
                  refine ⟨169297235496787935343447093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 225729647329050580457929457 169297235496787935343447093)
                  ·
                    refine ⟨15871615827823868938448165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 169297235496787935343447093 15871615827823868938448165)
                    ·
                      refine ⟨2975927967716975425959031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15871615827823868938448165 2975927967716975425959031)
                      ·
                        rfl

theorem cell23_5795599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 5, 4].length) (baseStart_5795599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5795599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5795599 prefixEnd_5795599 := by exact prefixLift 5795599
  have htrace : WordTrace (prefixWord ++ tailWord_5795599) baseStart_5795599 baseEnd_5795599 := by
    simpa [prefixWord, tailWord_5795599, baseEnd_5795599] using wordTrace_append hprefix tailTrace_5795599
  have hstable : (prefixWord ++ tailWord_5795599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5795599).length < 2 ^ (prefixWord ++ tailWord_5795599).sum := by decide
  have hdescent : baseEnd_5795599 < baseStart_5795599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5795599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5795633 : List Nat := [1, 2, 2, 3, 2, 2, 2, 3, 1, 1, 4]
def baseStart_5795633 : Nat := 118140960795 + 5795633 * 2 ^ 59
def prefixEnd_5795633 : Nat := 4983230072969 + 3 ^ 40 * 5795633 * 2
def baseEnd_5795633 : Nat := 2975945426059228292933875

theorem tailTrace_5795633 : CollatzResearch.WordTrace tailWord_5795633 prefixEnd_5795633 2975945426059228292933875 := by
  unfold tailWord_5795633
  simp only [CollatzResearch.WordTrace]
  refine ⟨211384101412418931158287553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140922734274945954105525035 211384101412418931158287553)
  ·
    refine ⟨158538076059314198368715665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211384101412418931158287553 158538076059314198368715665)
    ·
      refine ⟨118903557044485648776536749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158538076059314198368715665 118903557044485648776536749)
      ·
        refine ⟨44588833891682118291201281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118903557044485648776536749 44588833891682118291201281)
        ·
          refine ⟨33441625418761588718400961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44588833891682118291201281 33441625418761588718400961)
          ·
            refine ⟨25081219064071191538800721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33441625418761588718400961 25081219064071191538800721)
            ·
              refine ⟨18810914298053393654100541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25081219064071191538800721 18810914298053393654100541)
              ·
                refine ⟨7054092861770022620287703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18810914298053393654100541 7054092861770022620287703)
                ·
                  refine ⟨10581139292655033930431555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7054092861770022620287703 10581139292655033930431555)
                  ·
                    refine ⟨15871708938982550895647333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10581139292655033930431555 15871708938982550895647333)
                    ·
                      refine ⟨2975945426059228292933875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15871708938982550895647333 2975945426059228292933875)
                      ·
                        rfl

theorem cell23_5795633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_5795633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5795633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5795633 prefixEnd_5795633 := by exact prefixLift 5795633
  have htrace : WordTrace (prefixWord ++ tailWord_5795633) baseStart_5795633 baseEnd_5795633 := by
    simpa [prefixWord, tailWord_5795633, baseEnd_5795633] using wordTrace_append hprefix tailTrace_5795633
  have hstable : (prefixWord ++ tailWord_5795633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5795633).length < 2 ^ (prefixWord ++ tailWord_5795633).sum := by decide
  have hdescent : baseEnd_5795633 < baseStart_5795633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5795633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5795656 : List Nat := [2, 1, 3, 1, 1, 5, 2, 8]
def baseStart_5795656 : Nat := 118140960795 + 5795656 * 2 ^ 59
def prefixEnd_5795656 : Nat := 4983230072969 + 3 ^ 40 * 5795656 * 2
def baseEnd_5795656 : Nat := 110220638374603026035047

theorem tailTrace_5795656 : CollatzResearch.WordTrace tailWord_5795656 prefixEnd_5795656 110220638374603026035047 := by
  unfold tailWord_5795656
  simp only [CollatzResearch.WordTrace]
  refine ⟨105692470145667803043187411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140923293527557070724249881 105692470145667803043187411)
  ·
    refine ⟨158538705218501704564781117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105692470145667803043187411 158538705218501704564781117)
    ·
      refine ⟨59452014456938139211792919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158538705218501704564781117 59452014456938139211792919)
      ·
        refine ⟨89178021685407208817689379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59452014456938139211792919 89178021685407208817689379)
        ·
          refine ⟨133767032528110813226534069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89178021685407208817689379 133767032528110813226534069)
          ·
            refine ⟨12540659299510388739987569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 133767032528110813226534069 12540659299510388739987569)
            ·
              refine ⟨9405494474632791554990677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12540659299510388739987569 9405494474632791554990677)
              ·
                refine ⟨110220638374603026035047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9405494474632791554990677 110220638374603026035047)
                ·
                  rfl

theorem cell23_5795656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 8].length) (baseStart_5795656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5795656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5795656 prefixEnd_5795656 := by exact prefixLift 5795656
  have htrace : WordTrace (prefixWord ++ tailWord_5795656) baseStart_5795656 baseEnd_5795656 := by
    simpa [prefixWord, tailWord_5795656, baseEnd_5795656] using wordTrace_append hprefix tailTrace_5795656
  have hstable : (prefixWord ++ tailWord_5795656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5795656).length < 2 ^ (prefixWord ++ tailWord_5795656).sum := by decide
  have hdescent : baseEnd_5795656 < baseStart_5795656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5795656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5795660 : List Nat := [2, 2, 1, 3, 4, 1, 1, 3, 2, 4]
def baseStart_5795660 : Nat := 118140960795 + 5795660 * 2 ^ 59
def prefixEnd_5795660 : Nat := 4983230072969 + 3 ^ 40 * 5795660 * 2
def baseEnd_5795660 : Nat := 991986430012299895765417

theorem tailTrace_5795660 : CollatzResearch.WordTrace tailWord_5795660 prefixEnd_5795660 991986430012299895765417 := by
  unfold tailWord_5795660
  simp only [CollatzResearch.WordTrace]
  refine ⟨105692543091660557384760217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140923390788880743179680289 105692543091660557384760217)
  ·
    refine ⟨79269407318745418038570163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105692543091660557384760217 79269407318745418038570163)
    ·
      refine ⟨118904110978118127057855245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79269407318745418038570163 118904110978118127057855245)
      ·
        refine ⟨44589041616794297646695717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118904110978118127057855245 44589041616794297646695717)
        ·
          refine ⟨8360445303148930808755447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44589041616794297646695717 8360445303148930808755447)
          ·
            refine ⟨12540667954723396213133171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8360445303148930808755447 12540667954723396213133171)
            ·
              refine ⟨18811001932085094319699757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12540667954723396213133171 18811001932085094319699757)
              ·
                refine ⟨7054125724531910369887409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18811001932085094319699757 7054125724531910369887409)
                ·
                  refine ⟨5290594293398932777415557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7054125724531910369887409 5290594293398932777415557)
                  ·
                    refine ⟨991986430012299895765417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5290594293398932777415557 991986430012299895765417)
                    ·
                      rfl

theorem cell23_5795660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 3, 2, 4].length) (baseStart_5795660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5795660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5795660 prefixEnd_5795660 := by exact prefixLift 5795660
  have htrace : WordTrace (prefixWord ++ tailWord_5795660) baseStart_5795660 baseEnd_5795660 := by
    simpa [prefixWord, tailWord_5795660, baseEnd_5795660] using wordTrace_append hprefix tailTrace_5795660
  have hstable : (prefixWord ++ tailWord_5795660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5795660).length < 2 ^ (prefixWord ++ tailWord_5795660).sum := by decide
  have hdescent : baseEnd_5795660 < baseStart_5795660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5795660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5795706 : List Nat := [3, 1, 1, 1, 1, 1, 5, 1, 2, 3, 4]
def baseStart_5795706 : Nat := 118140960795 + 5795706 * 2 ^ 59
def prefixEnd_5795706 : Nat := 4983230072969 + 3 ^ 40 * 5795706 * 2
def baseEnd_5795706 : Nat := 2975982910147006507321039

theorem tailTrace_5795706 : CollatzResearch.WordTrace tailWord_5795706 prefixEnd_5795706 2975982910147006507321039 := by
  unfold tailWord_5795706
  simp only [CollatzResearch.WordTrace]
  refine ⟨52846690985288616156423743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140924509294102976417129981 52846690985288616156423743)
  ·
    refine ⟨79270036477932924234635615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52846690985288616156423743 79270036477932924234635615)
    ·
      refine ⟨118905054716899386351953423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79270036477932924234635615 118905054716899386351953423)
      ·
        refine ⟨178357582075349079527930135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118905054716899386351953423 178357582075349079527930135)
        ·
          refine ⟨267536373113023619291895203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178357582075349079527930135 267536373113023619291895203)
          ·
            refine ⟨401304559669535428937842805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267536373113023619291895203 401304559669535428937842805)
            ·
              refine ⟨37622302469018946462922763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 401304559669535428937842805 37622302469018946462922763)
              ·
                refine ⟨56433453703528419694384145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37622302469018946462922763 56433453703528419694384145)
                ·
                  refine ⟨42325090277646314770788109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56433453703528419694384145 42325090277646314770788109)
                  ·
                    refine ⟨15871908854117368039045541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42325090277646314770788109 15871908854117368039045541)
                    ·
                      refine ⟨2975982910147006507321039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15871908854117368039045541 2975982910147006507321039)
                      ·
                        rfl

theorem cell23_5795706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 2, 3, 4].length) (baseStart_5795706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5795706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5795706 prefixEnd_5795706 := by exact prefixLift 5795706
  have htrace : WordTrace (prefixWord ++ tailWord_5795706) baseStart_5795706 baseEnd_5795706 := by
    simpa [prefixWord, tailWord_5795706, baseEnd_5795706] using wordTrace_append hprefix tailTrace_5795706
  have hstable : (prefixWord ++ tailWord_5795706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5795706).length < 2 ^ (prefixWord ++ tailWord_5795706).sum := by decide
  have hdescent : baseEnd_5795706 < baseStart_5795706 := by decide
  rcases family_descends (prefixWord ++ tailWord_5795706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5795716 : List Nat := [2, 3, 2, 1, 1, 1, 3, 1, 1, 8]
def baseStart_5795716 : Nat := 118140960795 + 5795716 * 2 ^ 59
def prefixEnd_5795716 : Nat := 4983230072969 + 3 ^ 40 * 5795716 * 2
def baseEnd_5795716 : Nat := 991996014984517156065331

theorem tailTrace_5795716 : CollatzResearch.WordTrace tailWord_5795716 prefixEnd_5795716 991996014984517156065331 := by
  unfold tailWord_5795716
  simp only [CollatzResearch.WordTrace]
  refine ⟨105693564335559118166779501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140924752447412157555706001 105693564335559118166779501)
  ·
    refine ⟨39635086625834669312542313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105693564335559118166779501 39635086625834669312542313)
    ·
      refine ⟨29726314969376001984406735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39635086625834669312542313 29726314969376001984406735)
      ·
        refine ⟨44589472454064002976610103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29726314969376001984406735 44589472454064002976610103)
        ·
          refine ⟨66884208681096004464915155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44589472454064002976610103 66884208681096004464915155)
          ·
            refine ⟨100326313021644006697372733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66884208681096004464915155 100326313021644006697372733)
            ·
              refine ⟨37622367383116502511514775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100326313021644006697372733 37622367383116502511514775)
              ·
                refine ⟨56433551074674753767272163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37622367383116502511514775 56433551074674753767272163)
                ·
                  refine ⟨84650326612012130650908245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56433551074674753767272163 84650326612012130650908245)
                  ·
                    refine ⟨991996014984517156065331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 84650326612012130650908245 991996014984517156065331)
                    ·
                      rfl

theorem cell23_5795716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_5795716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5795716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5795716 prefixEnd_5795716 := by exact prefixLift 5795716
  have htrace : WordTrace (prefixWord ++ tailWord_5795716) baseStart_5795716 baseEnd_5795716 := by
    simpa [prefixWord, tailWord_5795716, baseEnd_5795716] using wordTrace_append hprefix tailTrace_5795716
  have hstable : (prefixWord ++ tailWord_5795716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5795716).length < 2 ^ (prefixWord ++ tailWord_5795716).sum := by decide
  have hdescent : baseEnd_5795716 < baseStart_5795716 := by decide
  rcases family_descends (prefixWord ++ tailWord_5795716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5795763 : List Nat := [1, 1, 1, 2, 3, 1, 3, 6, 5]
def baseStart_5795763 : Nat := 118140960795 + 5795763 * 2 ^ 59
def prefixEnd_5795763 : Nat := 4983230072969 + 3 ^ 40 * 5795763 * 2
def baseEnd_5795763 : Nat := 330668019838256976034253

theorem tailTrace_5795763 : CollatzResearch.WordTrace tailWord_5795763 prefixEnd_5795763 330668019838256976034253 := by
  unfold tailWord_5795763
  simp only [CollatzResearch.WordTrace]
  refine ⟨211388842901947963360519943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140925895267965308907013295 211388842901947963360519943)
  ·
    refine ⟨317083264352921945040779915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211388842901947963360519943 317083264352921945040779915)
    ·
      refine ⟨475624896529382917561169873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317083264352921945040779915 475624896529382917561169873)
      ·
        refine ⟨356718672397037188170877405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 475624896529382917561169873 356718672397037188170877405)
        ·
          refine ⟨133769502148888945564079027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 356718672397037188170877405 133769502148888945564079027)
          ·
            refine ⟨200654253223333418346118541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133769502148888945564079027 200654253223333418346118541)
            ·
              refine ⟨75245344958750031879794453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 200654253223333418346118541 75245344958750031879794453)
              ·
                refine ⟨3527125544941407744365365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 75245344958750031879794453 3527125544941407744365365)
                ·
                  refine ⟨330668019838256976034253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3527125544941407744365365 330668019838256976034253)
                  ·
                    rfl

theorem cell23_5795763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 6, 5].length) (baseStart_5795763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5795763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5795763 prefixEnd_5795763 := by exact prefixLift 5795763
  have htrace : WordTrace (prefixWord ++ tailWord_5795763) baseStart_5795763 baseEnd_5795763 := by
    simpa [prefixWord, tailWord_5795763, baseEnd_5795763] using wordTrace_append hprefix tailTrace_5795763
  have hstable : (prefixWord ++ tailWord_5795763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5795763).length < 2 ^ (prefixWord ++ tailWord_5795763).sum := by decide
  have hdescent : baseEnd_5795763 < baseStart_5795763 := by decide
  rcases family_descends (prefixWord ++ tailWord_5795763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5795776 : List Nat := [2, 1, 1, 2, 3, 2, 1, 1, 3, 7]
def baseStart_5795776 : Nat := 118140960795 + 5795776 * 2 ^ 59
def prefixEnd_5795776 : Nat := 4983230072969 + 3 ^ 40 * 5795776 * 2
def baseEnd_5795776 : Nat := 992006284597607077815239

theorem tailTrace_5795776 : CollatzResearch.WordTrace tailWord_5795776 prefixEnd_5795776 992006284597607077815239 := by
  unfold tailWord_5795776
  simp only [CollatzResearch.WordTrace]
  refine ⟨105694658525450433290371591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140926211367267244387162121 105694658525450433290371591)
  ·
    refine ⟨158541987788175649935557387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105694658525450433290371591 158541987788175649935557387)
    ·
      refine ⟨237812981682263474903336081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158541987788175649935557387 237812981682263474903336081)
      ·
        refine ⟨178359736261697606177502061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237812981682263474903336081 178359736261697606177502061)
        ·
          refine ⟨66884901098136602316563273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178359736261697606177502061 66884901098136602316563273)
          ·
            refine ⟨50163675823602451737422455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66884901098136602316563273 50163675823602451737422455)
            ·
              refine ⟨75245513735403677606133683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50163675823602451737422455 75245513735403677606133683)
              ·
                refine ⟨112868270603105516409200525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75245513735403677606133683 112868270603105516409200525)
                ·
                  refine ⟨42325601476164568653450197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112868270603105516409200525 42325601476164568653450197)
                  ·
                    refine ⟨992006284597607077815239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42325601476164568653450197 992006284597607077815239)
                    ·
                      rfl

theorem cell23_5795776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 3, 7].length) (baseStart_5795776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5795776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5795776 prefixEnd_5795776 := by exact prefixLift 5795776
  have htrace : WordTrace (prefixWord ++ tailWord_5795776) baseStart_5795776 baseEnd_5795776 := by
    simpa [prefixWord, tailWord_5795776, baseEnd_5795776] using wordTrace_append hprefix tailTrace_5795776
  have hstable : (prefixWord ++ tailWord_5795776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5795776).length < 2 ^ (prefixWord ++ tailWord_5795776).sum := by decide
  have hdescent : baseEnd_5795776 < baseStart_5795776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5795776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5795797 : List Nat := [1, 3, 2, 3, 2, 3, 1, 3, 5]
def baseStart_5795797 : Nat := 118140960795 + 5795797 * 2 ^ 59
def prefixEnd_5795797 : Nat := 4983230072969 + 3 ^ 40 * 5795797 * 2
def baseEnd_5795797 : Nat := 330669959654062850142569

theorem tailTrace_5795797 : CollatzResearch.WordTrace tailWord_5795797 prefixEnd_5795797 330669959654062850142569 := by
  unfold tailWord_5795797
  simp only [CollatzResearch.WordTrace]
  refine ⟨211390082983824787167257645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140926721989216524778171763 211390082983824787167257645)
  ·
    refine ⟨79271281118934295187721617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211390082983824787167257645 79271281118934295187721617)
    ·
      refine ⟨59453460839200721390791213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79271281118934295187721617 59453460839200721390791213)
      ·
        refine ⟨22295047814700270521546705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59453460839200721390791213 22295047814700270521546705)
        ·
          refine ⟨16721285861025202891160029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22295047814700270521546705 16721285861025202891160029)
          ·
            refine ⟨6270482197884451084185011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16721285861025202891160029 6270482197884451084185011)
            ·
              refine ⟨9405723296826676626277517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6270482197884451084185011 9405723296826676626277517)
              ·
                refine ⟨3527146236310003734854069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9405723296826676626277517 3527146236310003734854069)
                ·
                  refine ⟨330669959654062850142569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3527146236310003734854069 330669959654062850142569)
                  ·
                    rfl

theorem cell23_5795797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 3, 5].length) (baseStart_5795797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5795797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5795797 prefixEnd_5795797 := by exact prefixLift 5795797
  have htrace : WordTrace (prefixWord ++ tailWord_5795797) baseStart_5795797 baseEnd_5795797 := by
    simpa [prefixWord, tailWord_5795797, baseEnd_5795797] using wordTrace_append hprefix tailTrace_5795797
  have hstable : (prefixWord ++ tailWord_5795797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5795797).length < 2 ^ (prefixWord ++ tailWord_5795797).sum := by decide
  have hdescent : baseEnd_5795797 < baseStart_5795797 := by decide
  rcases family_descends (prefixWord ++ tailWord_5795797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5795900 : List Nat := [2, 2, 2, 2, 2, 1, 2, 4, 1, 5]
def baseStart_5795900 : Nat := 118140960795 + 5795900 * 2 ^ 59
def prefixEnd_5795900 : Nat := 4983230072969 + 3 ^ 40 * 5795900 * 2
def baseEnd_5795900 : Nat := 992027508464659582765049

theorem tailTrace_5795900 : CollatzResearch.WordTrace tailWord_5795900 prefixEnd_5795900 992027508464659582765049 := by
  unfold tailWord_5795900
  simp only [CollatzResearch.WordTrace]
  refine ⟨105696919851225817879128577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140929226468301090505504769 105696919851225817879128577)
  ·
    refine ⟨79272689888419363409346433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105696919851225817879128577 79272689888419363409346433)
    ·
      refine ⟨59454517416314522557009825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79272689888419363409346433 59454517416314522557009825)
      ·
        refine ⟨44590888062235891917757369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59454517416314522557009825 44590888062235891917757369)
        ·
          refine ⟨33443166046676918938318027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44590888062235891917757369 33443166046676918938318027)
          ·
            refine ⟨50164749070015378407477041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33443166046676918938318027 50164749070015378407477041)
            ·
              refine ⟨37623561802511533805607781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50164749070015378407477041 37623561802511533805607781)
              ·
                refine ⟨7054417837970912588551459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37623561802511533805607781 7054417837970912588551459)
                ·
                  refine ⟨10581626756956368882827189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7054417837970912588551459 10581626756956368882827189)
                  ·
                    refine ⟨992027508464659582765049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10581626756956368882827189 992027508464659582765049)
                    ·
                      rfl

theorem cell23_5795900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 4, 1, 5].length) (baseStart_5795900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5795900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5795900 prefixEnd_5795900 := by exact prefixLift 5795900
  have htrace : WordTrace (prefixWord ++ tailWord_5795900) baseStart_5795900 baseEnd_5795900 := by
    simpa [prefixWord, tailWord_5795900, baseEnd_5795900] using wordTrace_append hprefix tailTrace_5795900
  have hstable : (prefixWord ++ tailWord_5795900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5795900).length < 2 ^ (prefixWord ++ tailWord_5795900).sum := by decide
  have hdescent : baseEnd_5795900 < baseStart_5795900 := by decide
  rcases family_descends (prefixWord ++ tailWord_5795900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5795913 : List Nat := [1, 2, 1, 1, 2, 2, 3, 4, 1, 6]
def baseStart_5795913 : Nat := 118140960795 + 5795913 * 2 ^ 59
def prefixEnd_5795913 : Nat := 4983230072969 + 3 ^ 40 * 5795913 * 2
def baseEnd_5795913 : Nat := 992029733547495732477529

theorem tailTrace_5795913 : CollatzResearch.WordTrace tailWord_5795913 prefixEnd_5795913 992029733547495732477529 := by
  unfold tailWord_5795913
  simp only [CollatzResearch.WordTrace]
  refine ⟨211394313851404538978480393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140929542567603025985653595 211394313851404538978480393)
  ·
    refine ⟨158545735388553404233860295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211394313851404538978480393 158545735388553404233860295)
    ·
      refine ⟨237818603082830106350790443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158545735388553404233860295 237818603082830106350790443)
      ·
        refine ⟨356727904624245159526185665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237818603082830106350790443 356727904624245159526185665)
        ·
          refine ⟨267545928468183869644639249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 356727904624245159526185665 267545928468183869644639249)
          ·
            refine ⟨200659446351137902233479437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267545928468183869644639249 200659446351137902233479437)
            ·
              refine ⟨75247292381676713337554789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 200659446351137902233479437 75247292381676713337554789)
              ·
                refine ⟨14108867321564383750791523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75247292381676713337554789 14108867321564383750791523)
                ·
                  refine ⟨21163300982346575626187285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14108867321564383750791523 21163300982346575626187285)
                  ·
                    refine ⟨992029733547495732477529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21163300982346575626187285 992029733547495732477529)
                    ·
                      rfl

theorem cell23_5795913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 6].length) (baseStart_5795913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5795913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5795913 prefixEnd_5795913 := by exact prefixLift 5795913
  have htrace : WordTrace (prefixWord ++ tailWord_5795913) baseStart_5795913 baseEnd_5795913 := by
    simpa [prefixWord, tailWord_5795913, baseEnd_5795913] using wordTrace_append hprefix tailTrace_5795913
  have hstable : (prefixWord ++ tailWord_5795913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5795913).length < 2 ^ (prefixWord ++ tailWord_5795913).sum := by decide
  have hdescent : baseEnd_5795913 < baseStart_5795913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5795913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5795917 : List Nat := [1, 6, 1, 1, 1, 1, 3, 3, 1, 5]
def baseStart_5795917 : Nat := 118140960795 + 5795917 * 2 ^ 59
def prefixEnd_5795917 : Nat := 4983230072969 + 3 ^ 40 * 5795917 * 2
def baseEnd_5795917 : Nat := 992030418188368393927523

theorem tailTrace_5795917 : CollatzResearch.WordTrace tailWord_5795917 prefixEnd_5795917 992030418188368393927523 := by
  unfold tailWord_5795917
  simp only [CollatzResearch.WordTrace]
  refine ⟨211394459743390047661626005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140929639828926698441084003 211394459743390047661626005)
  ·
    refine ⟨9909115300471408484138719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 211394459743390047661626005 9909115300471408484138719)
    ·
      refine ⟨14863672950707112726208079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9909115300471408484138719 14863672950707112726208079)
      ·
        refine ⟨22295509426060669089312119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14863672950707112726208079 22295509426060669089312119)
        ·
          refine ⟨33443264139091003633968179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22295509426060669089312119 33443264139091003633968179)
          ·
            refine ⟨50164896208636505450952269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33443264139091003633968179 50164896208636505450952269)
            ·
              refine ⟨18811836078238689544107101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50164896208636505450952269 18811836078238689544107101)
              ·
                refine ⟨7054438529339508579040163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18811836078238689544107101 7054438529339508579040163)
                ·
                  refine ⟨10581657794009262868560245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7054438529339508579040163 10581657794009262868560245)
                  ·
                    refine ⟨992030418188368393927523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10581657794009262868560245 992030418188368393927523)
                    ·
                      rfl

theorem cell23_5795917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_5795917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5795917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5795917 prefixEnd_5795917 := by exact prefixLift 5795917
  have htrace : WordTrace (prefixWord ++ tailWord_5795917) baseStart_5795917 baseEnd_5795917 := by
    simpa [prefixWord, tailWord_5795917, baseEnd_5795917] using wordTrace_append hprefix tailTrace_5795917
  have hstable : (prefixWord ++ tailWord_5795917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5795917).length < 2 ^ (prefixWord ++ tailWord_5795917).sum := by decide
  have hdescent : baseEnd_5795917 < baseStart_5795917 := by decide
  rcases family_descends (prefixWord ++ tailWord_5795917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5795923 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 1, 8, 3]
def baseStart_5795923 : Nat := 118140960795 + 5795923 * 2 ^ 59
def prefixEnd_5795923 : Nat := 4983230072969 + 3 ^ 40 * 5795923 * 2
def baseEnd_5795923 : Nat := 2976094335449032158307541

theorem tailTrace_5795923 : CollatzResearch.WordTrace tailWord_5795923 prefixEnd_5795923 2976094335449032158307541 := by
  unfold tailWord_5795923
  simp only [CollatzResearch.WordTrace]
  refine ⟨211394678581368310686344423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140929785720912207124229615 211394678581368310686344423)
  ·
    refine ⟨317092017872052466029516635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211394678581368310686344423 317092017872052466029516635)
    ·
      refine ⟨475638026808078699044274953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317092017872052466029516635 475638026808078699044274953)
      ·
        refine ⟨356728520106059024283206215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 475638026808078699044274953 356728520106059024283206215)
        ·
          refine ⟨535092780159088536424809323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356728520106059024283206215 535092780159088536424809323)
          ·
            refine ⟨802639170238632804637213985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 535092780159088536424809323 802639170238632804637213985)
            ·
              refine ⟨601979377678974603477910489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 802639170238632804637213985 601979377678974603477910489)
              ·
                refine ⟨451484533259230952608432867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 601979377678974603477910489 451484533259230952608432867)
                ·
                  refine ⟨677226799888846428912649301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 451484533259230952608432867 677226799888846428912649301)
                  ·
                    refine ⟨7936251561197419088820109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 677226799888846428912649301 7936251561197419088820109)
                    ·
                      refine ⟨2976094335449032158307541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7936251561197419088820109 2976094335449032158307541)
                      ·
                        rfl

theorem cell23_5795923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 8, 3].length) (baseStart_5795923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5795923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5795923 prefixEnd_5795923 := by exact prefixLift 5795923
  have htrace : WordTrace (prefixWord ++ tailWord_5795923) baseStart_5795923 baseEnd_5795923 := by
    simpa [prefixWord, tailWord_5795923, baseEnd_5795923] using wordTrace_append hprefix tailTrace_5795923
  have hstable : (prefixWord ++ tailWord_5795923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5795923).length < 2 ^ (prefixWord ++ tailWord_5795923).sum := by decide
  have hdescent : baseEnd_5795923 < baseStart_5795923 := by decide
  rcases family_descends (prefixWord ++ tailWord_5795923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5795930 : List Nat := [3, 1, 1, 2, 1, 1, 5, 1, 4, 4]
def baseStart_5795930 : Nat := 118140960795 + 5795930 * 2 ^ 59
def prefixEnd_5795930 : Nat := 4983230072969 + 3 ^ 40 * 5795930 * 2
def baseEnd_5795930 : Nat := 992032643271204543640003

theorem tailTrace_5795930 : CollatzResearch.WordTrace tailWord_5795930 prefixEnd_5795930 992032643271204543640003 := by
  unfold tailWord_5795930
  simp only [CollatzResearch.WordTrace]
  refine ⟨52848733473085737720462311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140929955928228633921232829 52848733473085737720462311)
  ·
    refine ⟨79273100209628606580693467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52848733473085737720462311 79273100209628606580693467)
    ·
      refine ⟨118909650314442909871040201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79273100209628606580693467 118909650314442909871040201)
      ·
        refine ⟨89182237735832182403280151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118909650314442909871040201 89182237735832182403280151)
        ·
          refine ⟨133773356603748273604920227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89182237735832182403280151 133773356603748273604920227)
          ·
            refine ⟨200660034905622410407380341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133773356603748273604920227 200660034905622410407380341)
            ·
              refine ⟨18811878272402100975691907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 200660034905622410407380341 18811878272402100975691907)
              ·
                refine ⟨28217817408603151463537861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18811878272402100975691907 28217817408603151463537861)
                ·
                  refine ⟨5290840764113090899413349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28217817408603151463537861 5290840764113090899413349)
                  ·
                    refine ⟨992032643271204543640003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5290840764113090899413349 992032643271204543640003)
                    ·
                      rfl

theorem cell23_5795930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 4, 4].length) (baseStart_5795930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5795930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5795930 prefixEnd_5795930 := by exact prefixLift 5795930
  have htrace : WordTrace (prefixWord ++ tailWord_5795930) baseStart_5795930 baseEnd_5795930 := by
    simpa [prefixWord, tailWord_5795930, baseEnd_5795930] using wordTrace_append hprefix tailTrace_5795930
  have hstable : (prefixWord ++ tailWord_5795930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5795930).length < 2 ^ (prefixWord ++ tailWord_5795930).sum := by decide
  have hdescent : baseEnd_5795930 < baseStart_5795930 := by decide
  rcases family_descends (prefixWord ++ tailWord_5795930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5795940 : List Nat := [2, 3, 1, 1, 2, 1, 2, 1, 5, 2, 3]
def baseStart_5795940 : Nat := 118140960795 + 5795940 * 2 ^ 59
def prefixEnd_5795940 : Nat := 4983230072969 + 3 ^ 40 * 5795940 * 2
def baseEnd_5795940 : Nat := 2976103064620158591794963

theorem tailTrace_5795940 : CollatzResearch.WordTrace tailWord_5795940 prefixEnd_5795940 2976103064620158591794963 := by
  unfold tailWord_5795940
  simp only [CollatzResearch.WordTrace]
  refine ⟨105697649311153361294856637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140930199081537815059808849 105697649311153361294856637)
  ·
    refine ⟨39636618491682510485571239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105697649311153361294856637 39636618491682510485571239)
    ·
      refine ⟨59454927737523765728356859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39636618491682510485571239 59454927737523765728356859)
      ·
        refine ⟨89182391606285648592535289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59454927737523765728356859 89182391606285648592535289)
        ·
          refine ⟨66886793704714236444401467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89182391606285648592535289 66886793704714236444401467)
          ·
            refine ⟨100330190557071354666602201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66886793704714236444401467 100330190557071354666602201)
            ·
              refine ⟨75247642917803515999951651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100330190557071354666602201 75247642917803515999951651)
              ·
                refine ⟨112871464376705273999927477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75247642917803515999951651 112871464376705273999927477)
                ·
                  refine ⟨10581699785316119437493201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 112871464376705273999927477 10581699785316119437493201)
                  ·
                    refine ⟨7936274838987089578119901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10581699785316119437493201 7936274838987089578119901)
                    ·
                      refine ⟨2976103064620158591794963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7936274838987089578119901 2976103064620158591794963)
                      ·
                        rfl

theorem cell23_5795940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 5, 2, 3].length) (baseStart_5795940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5795940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5795940 prefixEnd_5795940 := by exact prefixLift 5795940
  have htrace : WordTrace (prefixWord ++ tailWord_5795940) baseStart_5795940 baseEnd_5795940 := by
    simpa [prefixWord, tailWord_5795940, baseEnd_5795940] using wordTrace_append hprefix tailTrace_5795940
  have hstable : (prefixWord ++ tailWord_5795940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5795940).length < 2 ^ (prefixWord ++ tailWord_5795940).sum := by decide
  have hdescent : baseEnd_5795940 < baseStart_5795940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5795940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5795943 : List Nat := [1, 1, 5, 1, 1, 2, 2, 10]
def baseStart_5795943 : Nat := 118140960795 + 5795943 * 2 ^ 59
def prefixEnd_5795943 : Nat := 4983230072969 + 3 ^ 40 * 5795943 * 2
def baseEnd_5795943 : Nat := 110226096483782299261387

theorem tailTrace_5795943 : CollatzResearch.WordTrace tailWord_5795943 prefixEnd_5795943 110226096483782299261387 := by
  unfold tailWord_5795943
  simp only [CollatzResearch.WordTrace]
  refine ⟨211395408041295854102072483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140930272027530569401381655 211395408041295854102072483)
  ·
    refine ⟨317093112061943781153108725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211395408041295854102072483 317093112061943781153108725)
    ·
      refine ⟨29727479255807229483103943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 317093112061943781153108725 29727479255807229483103943)
      ·
        refine ⟨44591218883710844224655915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29727479255807229483103943 44591218883710844224655915)
        ·
          refine ⟨66886828325566266336983873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44591218883710844224655915 66886828325566266336983873)
          ·
            refine ⟨50165121244174699752737905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66886828325566266336983873 50165121244174699752737905)
            ·
              refine ⟨37623840933131024814553429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50165121244174699752737905 37623840933131024814553429)
              ·
                refine ⟨110226096483782299261387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 37623840933131024814553429 110226096483782299261387)
                ·
                  rfl

theorem cell23_5795943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 10].length) (baseStart_5795943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5795943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5795943 prefixEnd_5795943 := by exact prefixLift 5795943
  have htrace : WordTrace (prefixWord ++ tailWord_5795943) baseStart_5795943 baseEnd_5795943 := by
    simpa [prefixWord, tailWord_5795943, baseEnd_5795943] using wordTrace_append hprefix tailTrace_5795943
  have hstable : (prefixWord ++ tailWord_5795943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5795943).length < 2 ^ (prefixWord ++ tailWord_5795943).sum := by decide
  have hdescent : baseEnd_5795943 < baseStart_5795943 := by decide
  rcases family_descends (prefixWord ++ tailWord_5795943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5795950 : List Nat := [4, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6]
def baseStart_5795950 : Nat := 118140960795 + 5795950 * 2 ^ 59
def prefixEnd_5795950 : Nat := 4983230072969 + 3 ^ 40 * 5795950 * 2
def baseEnd_5795950 : Nat := 2976108199426703552669917

theorem tailTrace_5795950 : CollatzResearch.WordTrace tailWord_5795950 prefixEnd_5795950 2976108199426703552669917 := by
  unfold tailWord_5795950
  simp only [CollatzResearch.WordTrace]
  refine ⟨26424457919033811787197163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140930442234846996198384869 26424457919033811787197163)
  ·
    refine ⟨39636686878550717680795745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26424457919033811787197163 39636686878550717680795745)
    ·
      refine ⟨29727515158913038260596809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39636686878550717680795745 29727515158913038260596809)
      ·
        refine ⟨22295636369184778695447607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29727515158913038260596809 22295636369184778695447607)
        ·
          refine ⟨33443454553777168043171411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22295636369184778695447607 33443454553777168043171411)
          ·
            refine ⟨50165181830665752064757117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33443454553777168043171411 50165181830665752064757117)
            ·
              refine ⟨18811943186499657024283919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50165181830665752064757117 18811943186499657024283919)
              ·
                refine ⟨28217914779749485536425879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18811943186499657024283919 28217914779749485536425879)
                ·
                  refine ⟨42326872169624228304638819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28217914779749485536425879 42326872169624228304638819)
                  ·
                    refine ⟨63490308254436342456958229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42326872169624228304638819 63490308254436342456958229)
                    ·
                      refine ⟨2976108199426703552669917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63490308254436342456958229 2976108199426703552669917)
                      ·
                        rfl

theorem cell23_5795950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_5795950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5795950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5795950 prefixEnd_5795950 := by exact prefixLift 5795950
  have htrace : WordTrace (prefixWord ++ tailWord_5795950) baseStart_5795950 baseEnd_5795950 := by
    simpa [prefixWord, tailWord_5795950, baseEnd_5795950] using wordTrace_append hprefix tailTrace_5795950
  have hstable : (prefixWord ++ tailWord_5795950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5795950).length < 2 ^ (prefixWord ++ tailWord_5795950).sum := by decide
  have hdescent : baseEnd_5795950 < baseStart_5795950 := by decide
  rcases family_descends (prefixWord ++ tailWord_5795950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5795954 : List Nat := [3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2]
def baseStart_5795954 : Nat := 118140960795 + 5795954 * 2 ^ 59
def prefixEnd_5795954 : Nat := 4983230072969 + 3 ^ 40 * 5795954 * 2
def baseEnd_5795954 : Nat := 2976110253349321537019899

theorem tailTrace_5795954 : CollatzResearch.WordTrace tailWord_5795954 prefixEnd_5795954 2976110253349321537019899 := by
  unfold tailWord_5795954
  simp only [CollatzResearch.WordTrace]
  refine ⟨52848952311064000745180729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140930539496170668653815277 52848952311064000745180729)
  ·
    refine ⟨39636714233298000558885547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52848952311064000745180729 39636714233298000558885547)
    ·
      refine ⟨59455071349947000838328321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39636714233298000558885547 59455071349947000838328321)
      ·
        refine ⟨44591303512460250628746241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59455071349947000838328321 44591303512460250628746241)
        ·
          refine ⟨33443477634345187971559681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44591303512460250628746241 33443477634345187971559681)
          ·
            refine ⟨25082608225758890978669761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33443477634345187971559681 25082608225758890978669761)
            ·
              refine ⟨18811956169319168234002321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25082608225758890978669761 18811956169319168234002321)
              ·
                refine ⟨14108967126989376175501741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18811956169319168234002321 14108967126989376175501741)
                ·
                  refine ⟨5290862672621016065813153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14108967126989376175501741 5290862672621016065813153)
                  ·
                    refine ⟨3968147004465762049359865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5290862672621016065813153 3968147004465762049359865)
                    ·
                      refine ⟨2976110253349321537019899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3968147004465762049359865 2976110253349321537019899)
                      ·
                        rfl

theorem cell23_5795954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2, 2].length) (baseStart_5795954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5795954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5795954 prefixEnd_5795954 := by exact prefixLift 5795954
  have htrace : WordTrace (prefixWord ++ tailWord_5795954) baseStart_5795954 baseEnd_5795954 := by
    simpa [prefixWord, tailWord_5795954, baseEnd_5795954] using wordTrace_append hprefix tailTrace_5795954
  have hstable : (prefixWord ++ tailWord_5795954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5795954).length < 2 ^ (prefixWord ++ tailWord_5795954).sum := by decide
  have hdescent : baseEnd_5795954 < baseStart_5795954 := by decide
  rcases family_descends (prefixWord ++ tailWord_5795954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5795971 : List Nat := [1, 1, 1, 3, 3, 3, 3, 3, 1, 2, 2]
def baseStart_5795971 : Nat := 118140960795 + 5795971 * 2 ^ 59
def prefixEnd_5795971 : Nat := 4983230072969 + 3 ^ 40 * 5795971 * 2
def baseEnd_5795971 : Nat := 2976118982520447970507321

theorem tailTrace_5795971 : CollatzResearch.WordTrace tailWord_5795971 prefixEnd_5795971 2976118982520447970507321 := by
  unfold tailWord_5795971
  simp only [CollatzResearch.WordTrace]
  refine ⟨211396429285194414884091767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140930952856796276589394511 211396429285194414884091767)
  ·
    refine ⟨317094643927791622326137651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211396429285194414884091767 317094643927791622326137651)
    ·
      refine ⟨475641965891687433489206477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317094643927791622326137651 475641965891687433489206477)
      ·
        refine ⟨178365737209382787558452429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 475641965891687433489206477 178365737209382787558452429)
        ·
          refine ⟨66887151453518545334419661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178365737209382787558452429 66887151453518545334419661)
          ·
            refine ⟨25082681795069454500407373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66887151453518545334419661 25082681795069454500407373)
            ·
              refine ⟨9406005673151045437652765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25082681795069454500407373 9406005673151045437652765)
              ·
                refine ⟨3527252127431642039119787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9406005673151045437652765 3527252127431642039119787)
                ·
                  refine ⟨5290878191147463058679681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3527252127431642039119787 5290878191147463058679681)
                  ·
                    refine ⟨3968158643360597294009761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5290878191147463058679681 3968158643360597294009761)
                    ·
                      refine ⟨2976118982520447970507321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3968158643360597294009761 2976118982520447970507321)
                      ·
                        rfl

theorem cell23_5795971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 1, 2, 2].length) (baseStart_5795971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5795971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5795971 prefixEnd_5795971 := by exact prefixLift 5795971
  have htrace : WordTrace (prefixWord ++ tailWord_5795971) baseStart_5795971 baseEnd_5795971 := by
    simpa [prefixWord, tailWord_5795971, baseEnd_5795971] using wordTrace_append hprefix tailTrace_5795971
  have hstable : (prefixWord ++ tailWord_5795971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5795971).length < 2 ^ (prefixWord ++ tailWord_5795971).sum := by decide
  have hdescent : baseEnd_5795971 < baseStart_5795971 := by decide
  rcases family_descends (prefixWord ++ tailWord_5795971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5795987 : List Nat := [1, 1, 1, 2, 1, 2, 3, 6, 2, 1, 3]
def baseStart_5795987 : Nat := 118140960795 + 5795987 * 2 ^ 59
def prefixEnd_5795987 : Nat := 4983230072969 + 3 ^ 40 * 5795987 * 2
def baseEnd_5795987 : Nat := 2976127198210919907907247

theorem tailTrace_5795987 : CollatzResearch.WordTrace tailWord_5795987 prefixEnd_5795987 2976127198210919907907247 := by
  unfold tailWord_5795987
  simp only [CollatzResearch.WordTrace]
  refine ⟨211397012853136449616674215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140931341902090966411116143 211397012853136449616674215)
  ·
    refine ⟨317095519279704674425011323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211397012853136449616674215 317095519279704674425011323)
    ·
      refine ⟨475643278919557011637516985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317095519279704674425011323 475643278919557011637516985)
      ·
        refine ⟨356732459189667758728137739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 475643278919557011637516985 356732459189667758728137739)
        ·
          refine ⟨535098688784501638092206609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356732459189667758728137739 535098688784501638092206609)
          ·
            refine ⟨401324016588376228569154957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 535098688784501638092206609 401324016588376228569154957)
            ·
              refine ⟨150496506220641085713433109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 401324016588376228569154957 150496506220641085713433109)
              ·
                refine ⟨7054523729092550892817177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 150496506220641085713433109 7054523729092550892817177)
                ·
                  refine ⟨5290892796819413169612883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7054523729092550892817177 5290892796819413169612883)
                  ·
                    refine ⟨7936339195229119754419325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5290892796819413169612883 7936339195229119754419325)
                    ·
                      refine ⟨2976127198210919907907247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7936339195229119754419325 2976127198210919907907247)
                      ·
                        rfl

theorem cell23_5795987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 6, 2, 1, 3].length) (baseStart_5795987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5795987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5795987 prefixEnd_5795987 := by exact prefixLift 5795987
  have htrace : WordTrace (prefixWord ++ tailWord_5795987) baseStart_5795987 baseEnd_5795987 := by
    simpa [prefixWord, tailWord_5795987, baseEnd_5795987] using wordTrace_append hprefix tailTrace_5795987
  have hstable : (prefixWord ++ tailWord_5795987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5795987).length < 2 ^ (prefixWord ++ tailWord_5795987).sum := by decide
  have hdescent : baseEnd_5795987 < baseStart_5795987 := by decide
  rcases family_descends (prefixWord ++ tailWord_5795987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5795998 : List Nat := [4, 3, 1, 1, 3, 2, 2, 1, 2, 4]
def baseStart_5795998 : Nat := 118140960795 + 5795998 * 2 ^ 59
def prefixEnd_5795998 : Nat := 4983230072969 + 3 ^ 40 * 5795998 * 2
def baseEnd_5795998 : Nat := 992044282166039788289899

theorem tailTrace_5795998 : CollatzResearch.WordTrace tailWord_5795998 prefixEnd_5795998 992044282166039788289899 := by
  unfold tailWord_5795998
  simp only [CollatzResearch.WordTrace]
  refine ⟨26424676757012074811915581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140931609370731065663549765 26424676757012074811915581)
  ·
    refine ⟨9909253783879528054468343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26424676757012074811915581 9909253783879528054468343)
    ·
      refine ⟨14863880675819292081702515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9909253783879528054468343 14863880675819292081702515)
      ·
        refine ⟨22295821013728938122553773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14863880675819292081702515 22295821013728938122553773)
        ·
          refine ⟨8360932880148351795957665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22295821013728938122553773 8360932880148351795957665)
          ·
            refine ⟨6270699660111263846968249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8360932880148351795957665 6270699660111263846968249)
            ·
              refine ⟨4703024745083447885226187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6270699660111263846968249 4703024745083447885226187)
              ·
                refine ⟨7054537117625171827839281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4703024745083447885226187 7054537117625171827839281)
                ·
                  refine ⟨5290902838218878870879461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7054537117625171827839281 5290902838218878870879461)
                  ·
                    refine ⟨992044282166039788289899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5290902838218878870879461 992044282166039788289899)
                    ·
                      rfl

theorem cell23_5795998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_5795998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5795998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5795998 prefixEnd_5795998 := by exact prefixLift 5795998
  have htrace : WordTrace (prefixWord ++ tailWord_5795998) baseStart_5795998 baseEnd_5795998 := by
    simpa [prefixWord, tailWord_5795998, baseEnd_5795998] using wordTrace_append hprefix tailTrace_5795998
  have hstable : (prefixWord ++ tailWord_5795998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5795998).length < 2 ^ (prefixWord ++ tailWord_5795998).sum := by decide
  have hdescent : baseEnd_5795998 < baseStart_5795998 := by decide
  rcases family_descends (prefixWord ++ tailWord_5795998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796027 : List Nat := [1, 1, 1, 1, 1, 2, 7, 2, 1, 4, 2]
def baseStart_5796027 : Nat := 118140960795 + 5796027 * 2 ^ 59
def prefixEnd_5796027 : Nat := 4983230072969 + 3 ^ 40 * 5796027 * 2
def baseEnd_5796027 : Nat := 2976147737437099751407063

theorem tailTrace_5796027 : CollatzResearch.WordTrace tailWord_5796027 prefixEnd_5796027 2976147737437099751407063 := by
  unfold tailWord_5796027
  simp only [CollatzResearch.WordTrace]
  refine ⟨211398471772991536448130335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140932314515327690965420223 211398471772991536448130335)
  ·
    refine ⟨317097707659487304672195503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211398471772991536448130335 317097707659487304672195503)
    ·
      refine ⟨475646561489230957008293255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317097707659487304672195503 475646561489230957008293255)
      ·
        refine ⟨713469842233846435512439883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475646561489230957008293255 713469842233846435512439883)
        ·
          refine ⟨1070204763350769653268659825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 713469842233846435512439883 1070204763350769653268659825)
          ·
            refine ⟨802653572513077239951494869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1070204763350769653268659825 802653572513077239951494869)
            ·
              refine ⟨18812193105775247811363161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 802653572513077239951494869 18812193105775247811363161)
              ·
                refine ⟨14109144829331435858522371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18812193105775247811363161 14109144829331435858522371)
                ·
                  refine ⟨21163717243997153787783557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14109144829331435858522371 21163717243997153787783557)
                  ·
                    refine ⟨3968196983249466335209417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21163717243997153787783557 3968196983249466335209417)
                    ·
                      refine ⟨2976147737437099751407063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3968196983249466335209417 2976147737437099751407063)
                      ·
                        rfl

theorem cell23_5796027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 4, 2].length) (baseStart_5796027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796027 prefixEnd_5796027 := by exact prefixLift 5796027
  have htrace : WordTrace (prefixWord ++ tailWord_5796027) baseStart_5796027 baseEnd_5796027 := by
    simpa [prefixWord, tailWord_5796027, baseEnd_5796027] using wordTrace_append hprefix tailTrace_5796027
  have hstable : (prefixWord ++ tailWord_5796027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796027).length < 2 ^ (prefixWord ++ tailWord_5796027).sum := by decide
  have hdescent : baseEnd_5796027 < baseStart_5796027 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796040 : List Nat := [2, 1, 3, 1, 2, 1, 1, 4, 2, 2, 4]
def baseStart_5796040 : Nat := 118140960795 + 5796040 * 2 ^ 59
def prefixEnd_5796040 : Nat := 4983230072969 + 3 ^ 40 * 5796040 * 2
def baseEnd_5796040 : Nat := 2976154412685608200544503

theorem tailTrace_5796040 : CollatzResearch.WordTrace tailWord_5796040 prefixEnd_5796040 2976154412685608200544503 := by
  unfold tailWord_5796040
  simp only [CollatzResearch.WordTrace]
  refine ⟨105699472960972219834176787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140932630614629626445569049 105699472960972219834176787)
  ·
    refine ⟨158549209441458329751265181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105699472960972219834176787 158549209441458329751265181)
    ·
      refine ⟨59455953540546873656724443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158549209441458329751265181 59455953540546873656724443)
      ·
        refine ⟨89183930310820310485086665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59455953540546873656724443 89183930310820310485086665)
        ·
          refine ⟨66887947733115232863814999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89183930310820310485086665 66887947733115232863814999)
          ·
            refine ⟨100331921599672849295722499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66887947733115232863814999 100331921599672849295722499)
            ·
              refine ⟨150497882399509273943583749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100331921599672849295722499 150497882399509273943583749)
              ·
                refine ⟨28218352949907988864421953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 150497882399509273943583749 28218352949907988864421953)
                ·
                  refine ⟨21163764712430991648316465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28218352949907988864421953 21163764712430991648316465)
                  ·
                    refine ⟨15872823534323243736237349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21163764712430991648316465 15872823534323243736237349)
                    ·
                      refine ⟨2976154412685608200544503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15872823534323243736237349 2976154412685608200544503)
                      ·
                        rfl

theorem cell23_5796040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_5796040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796040 prefixEnd_5796040 := by exact prefixLift 5796040
  have htrace : WordTrace (prefixWord ++ tailWord_5796040) baseStart_5796040 baseEnd_5796040 := by
    simpa [prefixWord, tailWord_5796040, baseEnd_5796040] using wordTrace_append hprefix tailTrace_5796040
  have hstable : (prefixWord ++ tailWord_5796040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796040).length < 2 ^ (prefixWord ++ tailWord_5796040).sum := by decide
  have hdescent : baseEnd_5796040 < baseStart_5796040 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796054 : List Nat := [5, 2, 1, 2, 1, 2, 1, 1, 2, 6]
def baseStart_5796054 : Nat := 118140960795 + 5796054 * 2 ^ 59
def prefixEnd_5796054 : Nat := 4983230072969 + 3 ^ 40 * 5796054 * 2
def baseEnd_5796054 : Nat := 992053867138257048589813

theorem tailTrace_5796054 : CollatzResearch.WordTrace tailWord_5796054 prefixEnd_5796054 992053867138257048589813 := by
  unfold tailWord_5796054
  simp only [CollatzResearch.WordTrace]
  refine ⟨13212466033993357503710201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 140932971029262480039575477 13212466033993357503710201)
  ·
    refine ⟨9909349525495018127782651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13212466033993357503710201 9909349525495018127782651)
    ·
      refine ⟨14864024288242527191673977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9909349525495018127782651 14864024288242527191673977)
      ·
        refine ⟨11148018216181895393755483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14864024288242527191673977 11148018216181895393755483)
        ·
          refine ⟨16722027324272843090633225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11148018216181895393755483 16722027324272843090633225)
          ·
            refine ⟨12541520493204632317974919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16722027324272843090633225 12541520493204632317974919)
            ·
              refine ⟨18812280739806948476962379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12541520493204632317974919 18812280739806948476962379)
              ·
                refine ⟨28218421109710422715443569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18812280739806948476962379 28218421109710422715443569)
                ·
                  refine ⟨21163815832282817036582677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28218421109710422715443569 21163815832282817036582677)
                  ·
                    refine ⟨992053867138257048589813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21163815832282817036582677 992053867138257048589813)
                    ·
                      rfl

theorem cell23_5796054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_5796054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796054 prefixEnd_5796054 := by exact prefixLift 5796054
  have htrace : WordTrace (prefixWord ++ tailWord_5796054) baseStart_5796054 baseEnd_5796054 := by
    simpa [prefixWord, tailWord_5796054, baseEnd_5796054] using wordTrace_append hprefix tailTrace_5796054
  have hstable : (prefixWord ++ tailWord_5796054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796054).length < 2 ^ (prefixWord ++ tailWord_5796054).sum := by decide
  have hdescent : baseEnd_5796054 < baseStart_5796054 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796061 : List Nat := [1, 4, 3, 2, 1, 2, 2, 1, 1, 4, 2]
def baseStart_5796061 : Nat := 118140960795 + 5796061 * 2 ^ 59
def prefixEnd_5796061 : Nat := 4983230072969 + 3 ^ 40 * 5796061 * 2
def baseEnd_5796061 : Nat := 2976165195779352618381907

theorem tailTrace_5796061 : CollatzResearch.WordTrace tailWord_5796061 prefixEnd_5796061 2976165195779352618381907 := by
  unfold tailWord_5796061
  simp only [CollatzResearch.WordTrace]
  refine ⟨211399711854868360254868037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140933141236578906836578691 211399711854868360254868037)
  ·
    refine ⟨39637445972787817547787757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 211399711854868360254868037 39637445972787817547787757)
    ·
      refine ⟨14864042239795431580420409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39637445972787817547787757 14864042239795431580420409)
      ·
        refine ⟨11148031679846573685315307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14864042239795431580420409 11148031679846573685315307)
        ·
          refine ⟨16722047519769860527972961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11148031679846573685315307 16722047519769860527972961)
          ·
            refine ⟨12541535639827395395979721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16722047519769860527972961 12541535639827395395979721)
            ·
              refine ⟨9406151729870546546984791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12541535639827395395979721 9406151729870546546984791)
              ·
                refine ⟨14109227594805819820477187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9406151729870546546984791 14109227594805819820477187)
                ·
                  refine ⟨21163841392208729730715781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14109227594805819820477187 21163841392208729730715781)
                  ·
                    refine ⟨3968220261039136824509209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21163841392208729730715781 3968220261039136824509209)
                    ·
                      refine ⟨2976165195779352618381907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3968220261039136824509209 2976165195779352618381907)
                      ·
                        rfl

theorem cell23_5796061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_5796061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796061 prefixEnd_5796061 := by exact prefixLift 5796061
  have htrace : WordTrace (prefixWord ++ tailWord_5796061) baseStart_5796061 baseEnd_5796061 := by
    simpa [prefixWord, tailWord_5796061, baseEnd_5796061] using wordTrace_append hprefix tailTrace_5796061
  have hstable : (prefixWord ++ tailWord_5796061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796061).length < 2 ^ (prefixWord ++ tailWord_5796061).sum := by decide
  have hdescent : baseEnd_5796061 < baseStart_5796061 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796135 : List Nat := [1, 1, 8, 1, 1, 2, 1, 3, 5]
def baseStart_5796135 : Nat := 118140960795 + 5796135 * 2 ^ 59
def prefixEnd_5796135 : Nat := 4983230072969 + 3 ^ 40 * 5796135 * 2
def baseEnd_5796135 : Nat := 330689243705309480984063

theorem tailTrace_5796135 : CollatzResearch.WordTrace tailWord_5796135 prefixEnd_5796135 330689243705309480984063 := by
  unfold tailWord_5796135
  simp only [CollatzResearch.WordTrace]
  refine ⟨211402410856600270893061859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140934940571066847262041239 211402410856600270893061859)
  ·
    refine ⟨317103616284900406339592789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211402410856600270893061859 317103616284900406339592789)
    ·
      refine ⟨3716058003338676636792103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 317103616284900406339592789 3716058003338676636792103)
      ·
        refine ⟨5574087005008014955188155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3716058003338676636792103 5574087005008014955188155)
        ·
          refine ⟨8361130507512022432782233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5574087005008014955188155 8361130507512022432782233)
          ·
            refine ⟨6270847880634016824586675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8361130507512022432782233 6270847880634016824586675)
            ·
              refine ⟨9406271820951025236880013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6270847880634016824586675 9406271820951025236880013)
              ·
                refine ⟨3527351932856634463830005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9406271820951025236880013 3527351932856634463830005)
                ·
                  refine ⟨330689243705309480984063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3527351932856634463830005 330689243705309480984063)
                  ·
                    rfl

theorem cell23_5796135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 3, 5].length) (baseStart_5796135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796135 prefixEnd_5796135 := by exact prefixLift 5796135
  have htrace : WordTrace (prefixWord ++ tailWord_5796135) baseStart_5796135 baseEnd_5796135 := by
    simpa [prefixWord, tailWord_5796135, baseEnd_5796135] using wordTrace_append hprefix tailTrace_5796135
  have hstable : (prefixWord ++ tailWord_5796135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796135).length < 2 ^ (prefixWord ++ tailWord_5796135).sum := by decide
  have hdescent : baseEnd_5796135 < baseStart_5796135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796140 : List Nat := [2, 2, 1, 1, 1, 3, 3, 2, 8]
def baseStart_5796140 : Nat := 118140960795 + 5796140 * 2 ^ 59
def prefixEnd_5796140 : Nat := 4983230072969 + 3 ^ 40 * 5796140 * 2
def baseEnd_5796140 : Nat := 330689528972339756588227

theorem tailTrace_5796140 : CollatzResearch.WordTrace tailWord_5796140 prefixEnd_5796140 330689528972339756588227 := by
  unfold tailWord_5796140
  simp only [CollatzResearch.WordTrace]
  refine ⟨105701296610791078373496937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140935062147721437831329249 105701296610791078373496937)
  ·
    refine ⟨79275972458093308780122703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105701296610791078373496937 79275972458093308780122703)
    ·
      refine ⟨118913958687139963170184055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79275972458093308780122703 118913958687139963170184055)
      ·
        refine ⟨178370938030709944755276083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118913958687139963170184055 178370938030709944755276083)
        ·
          refine ⟨267556407046064917132914125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178370938030709944755276083 267556407046064917132914125)
          ·
            refine ⟨100333652642274343924842797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 267556407046064917132914125 100333652642274343924842797)
            ·
              refine ⟨37625119740852878971816049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100333652642274343924842797 37625119740852878971816049)
              ·
                refine ⟨28218839805639659228862037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37625119740852878971816049 28218839805639659228862037)
                ·
                  refine ⟨330689528972339756588227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28218839805639659228862037 330689528972339756588227)
                  ·
                    rfl

theorem cell23_5796140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 8].length) (baseStart_5796140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796140 prefixEnd_5796140 := by exact prefixLift 5796140
  have htrace : WordTrace (prefixWord ++ tailWord_5796140) baseStart_5796140 baseEnd_5796140 := by
    simpa [prefixWord, tailWord_5796140, baseEnd_5796140] using wordTrace_append hprefix tailTrace_5796140
  have hstable : (prefixWord ++ tailWord_5796140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796140).length < 2 ^ (prefixWord ++ tailWord_5796140).sum := by decide
  have hdescent : baseEnd_5796140 < baseStart_5796140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796144 : List Nat := [2, 1, 1, 1, 2, 2, 2, 7, 1, 4]
def baseStart_5796144 : Nat := 118140960795 + 5796144 * 2 ^ 59
def prefixEnd_5796144 : Nat := 4983230072969 + 3 ^ 40 * 5796144 * 2
def baseEnd_5796144 : Nat := 992069271557891931214675

theorem tailTrace_5796144 : CollatzResearch.WordTrace tailWord_5796144 prefixEnd_5796144 992069271557891931214675 := by
  unfold tailWord_5796144
  simp only [CollatzResearch.WordTrace]
  refine ⟨105701369556783832715069743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140935159409045110286759657 105701369556783832715069743)
  ·
    refine ⟨158552054335175749072604615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105701369556783832715069743 158552054335175749072604615)
    ·
      refine ⟨237828081502763623608906923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158552054335175749072604615 237828081502763623608906923)
      ·
        refine ⟨356742122254145435413360385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237828081502763623608906923 356742122254145435413360385)
        ·
          refine ⟨267556591690609076560020289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 356742122254145435413360385 267556591690609076560020289)
          ·
            refine ⟨200667443767956807420015217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267556591690609076560020289 200667443767956807420015217)
            ·
              refine ⟨150500582825967605565011413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200667443767956807420015217 150500582825967605565011413)
              ·
                refine ⟨3527357409983615755429955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 150500582825967605565011413 3527357409983615755429955)
                ·
                  refine ⟨5291036114975423633144933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3527357409983615755429955 5291036114975423633144933)
                  ·
                    refine ⟨992069271557891931214675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5291036114975423633144933 992069271557891931214675)
                    ·
                      rfl

theorem cell23_5796144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 7, 1, 4].length) (baseStart_5796144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796144 prefixEnd_5796144 := by exact prefixLift 5796144
  have htrace : WordTrace (prefixWord ++ tailWord_5796144) baseStart_5796144 baseEnd_5796144 := by
    simpa [prefixWord, tailWord_5796144, baseEnd_5796144] using wordTrace_append hprefix tailTrace_5796144
  have hstable : (prefixWord ++ tailWord_5796144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796144).length < 2 ^ (prefixWord ++ tailWord_5796144).sum := by decide
  have hdescent : baseEnd_5796144 < baseStart_5796144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796154 : List Nat := [3, 1, 1, 1, 4, 3, 1, 2, 2, 2, 3]
def baseStart_5796154 : Nat := 118140960795 + 5796154 * 2 ^ 59
def prefixEnd_5796154 : Nat := 4983230072969 + 3 ^ 40 * 5796154 * 2
def baseEnd_5796154 : Nat := 2976212949480220754518979

theorem tailTrace_5796154 : CollatzResearch.WordTrace tailWord_5796154 prefixEnd_5796154 2976212949480220754518979 := by
  unfold tailWord_5796154
  simp only [CollatzResearch.WordTrace]
  refine ⟨52850775960882859284500879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140935402562354291425335677 52850775960882859284500879)
  ·
    refine ⟨79276163941324288926751319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52850775960882859284500879 79276163941324288926751319)
    ·
      refine ⟨118914245911986433390126979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79276163941324288926751319 118914245911986433390126979)
      ·
        refine ⟨178371368867979650085190469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118914245911986433390126979 178371368867979650085190469)
        ·
          refine ⟨33444631662746184390973213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 178371368867979650085190469 33444631662746184390973213)
          ·
            refine ⟨12541736873529819146614955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33444631662746184390973213 12541736873529819146614955)
            ·
              refine ⟨18812605310294728719922433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12541736873529819146614955 18812605310294728719922433)
              ·
                refine ⟨14109453982721046539941825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18812605310294728719922433 14109453982721046539941825)
                ·
                  refine ⟨10582090487040784904956369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14109453982721046539941825 10582090487040784904956369)
                  ·
                    refine ⟨7936567865280588678717277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10582090487040784904956369 7936567865280588678717277)
                    ·
                      refine ⟨2976212949480220754518979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7936567865280588678717277 2976212949480220754518979)
                      ·
                        rfl

theorem cell23_5796154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 2, 2, 3].length) (baseStart_5796154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796154 prefixEnd_5796154 := by exact prefixLift 5796154
  have htrace : WordTrace (prefixWord ++ tailWord_5796154) baseStart_5796154 baseEnd_5796154 := by
    simpa [prefixWord, tailWord_5796154, baseEnd_5796154] using wordTrace_append hprefix tailTrace_5796154
  have hstable : (prefixWord ++ tailWord_5796154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796154).length < 2 ^ (prefixWord ++ tailWord_5796154).sum := by decide
  have hdescent : baseEnd_5796154 < baseStart_5796154 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796160 : List Nat := [2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 6]
def baseStart_5796160 : Nat := 118140960795 + 5796160 * 2 ^ 59
def prefixEnd_5796160 : Nat := 4983230072969 + 3 ^ 40 * 5796160 * 2
def baseEnd_5796160 : Nat := 2976216030364147731043951

theorem tailTrace_5796160 : CollatzResearch.WordTrace tailWord_5796160 prefixEnd_5796160 2976216030364147731043951 := by
  unfold tailWord_5796160
  simp only [CollatzResearch.WordTrace]
  refine ⟨105701661340754850081360967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140935548454339800108481289 105701661340754850081360967)
  ·
    refine ⟨158552492011132275122041451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105701661340754850081360967 158552492011132275122041451)
    ·
      refine ⟨237828738016698412683062177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158552492011132275122041451 237828738016698412683062177)
      ·
        refine ⟨178371553512523809512296633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237828738016698412683062177 178371553512523809512296633)
        ·
          refine ⟨133778665134392857134222475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178371553512523809512296633 133778665134392857134222475)
          ·
            refine ⟨200667997701589285701333713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133778665134392857134222475 200667997701589285701333713)
            ·
              refine ⟨150500998276191964276000285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200667997701589285701333713 150500998276191964276000285)
              ·
                refine ⟨56437874353571986603500107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150500998276191964276000285 56437874353571986603500107)
                ·
                  refine ⟨84656811530357979905250161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56437874353571986603500107 84656811530357979905250161)
                  ·
                    refine ⟨63492608647768484928937621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 84656811530357979905250161 63492608647768484928937621)
                    ·
                      refine ⟨2976216030364147731043951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63492608647768484928937621 2976216030364147731043951)
                      ·
                        rfl

theorem cell23_5796160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 6].length) (baseStart_5796160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796160 prefixEnd_5796160 := by exact prefixLift 5796160
  have htrace : WordTrace (prefixWord ++ tailWord_5796160) baseStart_5796160 baseEnd_5796160 := by
    simpa [prefixWord, tailWord_5796160, baseEnd_5796160] using wordTrace_append hprefix tailTrace_5796160
  have hstable : (prefixWord ++ tailWord_5796160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796160).length < 2 ^ (prefixWord ++ tailWord_5796160).sum := by decide
  have hdescent : baseEnd_5796160 < baseStart_5796160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796170 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 1, 11]
def baseStart_5796170 : Nat := 118140960795 + 5796170 * 2 ^ 59
def prefixEnd_5796170 : Nat := 4983230072969 + 3 ^ 40 * 5796170 * 2
def baseEnd_5796170 : Nat := 992073721723564230639635

theorem tailTrace_5796170 : CollatzResearch.WordTrace tailWord_5796170 prefixEnd_5796170 992073721723564230639635 := by
  unfold tailWord_5796170
  simp only [CollatzResearch.WordTrace]
  refine ⟨52850921852868367967646491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140935791607648981247057309 52850921852868367967646491)
  ·
    refine ⟨79276382779302551951469737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52850921852868367967646491 79276382779302551951469737)
    ·
      refine ⟨59457287084476913963602303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79276382779302551951469737 59457287084476913963602303)
      ·
        refine ⟨89185930626715370945403455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59457287084476913963602303 89185930626715370945403455)
        ·
          refine ⟨133778895940073056418105183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89185930626715370945403455 133778895940073056418105183)
          ·
            refine ⟨200668343910109584627157775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133778895940073056418105183 200668343910109584627157775)
            ·
              refine ⟨301002515865164376940736663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200668343910109584627157775 301002515865164376940736663)
              ·
                refine ⟨451503773797746565411104995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 301002515865164376940736663 451503773797746565411104995)
                ·
                  refine ⟨677255660696619848116657493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 451503773797746565411104995 677255660696619848116657493)
                  ·
                    refine ⟨992073721723564230639635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 677255660696619848116657493 992073721723564230639635)
                    ·
                      rfl

theorem cell23_5796170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 1, 11].length) (baseStart_5796170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796170 prefixEnd_5796170 := by exact prefixLift 5796170
  have htrace : WordTrace (prefixWord ++ tailWord_5796170) baseStart_5796170 baseEnd_5796170 := by
    simpa [prefixWord, tailWord_5796170, baseEnd_5796170] using wordTrace_append hprefix tailTrace_5796170
  have hstable : (prefixWord ++ tailWord_5796170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796170).length < 2 ^ (prefixWord ++ tailWord_5796170).sum := by decide
  have hdescent : baseEnd_5796170 < baseStart_5796170 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796188 : List Nat := [2, 2, 4, 3, 1, 1, 2, 1, 2, 2, 3]
def baseStart_5796188 : Nat := 118140960795 + 5796188 * 2 ^ 59
def prefixEnd_5796188 : Nat := 4983230072969 + 3 ^ 40 * 5796188 * 2
def baseEnd_5796188 : Nat := 2976230407822473621493823

theorem tailTrace_5796188 : CollatzResearch.WordTrace tailWord_5796188 prefixEnd_5796188 2976230407822473621493823 := by
  unfold tailWord_5796188
  simp only [CollatzResearch.WordTrace]
  refine ⟨105702171962704130472370609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140936229283605507296494145 105702171962704130472370609)
  ·
    refine ⟨79276628972028097854277957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105702171962704130472370609 79276628972028097854277957)
    ·
      refine ⟨14864367932255268347677117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79276628972028097854277957 14864367932255268347677117)
      ·
        refine ⟨5574137974595725630378919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14864367932255268347677117 5574137974595725630378919)
        ·
          refine ⟨8361206961893588445568379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5574137974595725630378919 8361206961893588445568379)
          ·
            refine ⟨12541810442840382668352569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8361206961893588445568379 12541810442840382668352569)
            ·
              refine ⟨9406357832130287001264427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12541810442840382668352569 9406357832130287001264427)
              ·
                refine ⟨14109536748195430501896641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9406357832130287001264427 14109536748195430501896641)
                ·
                  refine ⟨10582152561146572876422481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14109536748195430501896641 10582152561146572876422481)
                  ·
                    refine ⟨7936614420859929657316861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10582152561146572876422481 7936614420859929657316861)
                    ·
                      refine ⟨2976230407822473621493823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7936614420859929657316861 2976230407822473621493823)
                      ·
                        rfl

theorem cell23_5796188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_5796188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796188 prefixEnd_5796188 := by exact prefixLift 5796188
  have htrace : WordTrace (prefixWord ++ tailWord_5796188) baseStart_5796188 baseEnd_5796188 := by
    simpa [prefixWord, tailWord_5796188, baseEnd_5796188] using wordTrace_append hprefix tailTrace_5796188
  have hstable : (prefixWord ++ tailWord_5796188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796188).length < 2 ^ (prefixWord ++ tailWord_5796188).sum := by decide
  have hdescent : baseEnd_5796188 < baseStart_5796188 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796201 : List Nat := [1, 2, 1, 1, 1, 3, 4, 5, 1, 1, 3]
def baseStart_5796201 : Nat := 118140960795 + 5796201 * 2 ^ 59
def prefixEnd_5796201 : Nat := 4983230072969 + 3 ^ 40 * 5796201 * 2
def baseEnd_5796201 : Nat := 2976237083070982070631263

theorem tailTrace_5796201 : CollatzResearch.WordTrace tailWord_5796201 prefixEnd_5796201 2976237083070982070631263 := by
  unfold tailWord_5796201
  simp only [CollatzResearch.WordTrace]
  refine ⟨211404818074361164164964457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140936545382907442776642971 211404818074361164164964457)
  ·
    refine ⟨158553613555770873123723343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211404818074361164164964457 158553613555770873123723343)
    ·
      refine ⟨237830420333656309685585015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158553613555770873123723343 237830420333656309685585015)
      ·
        refine ⟨356745630500484464528377523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237830420333656309685585015 356745630500484464528377523)
        ·
          refine ⟨535118445750726696792566285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356745630500484464528377523 535118445750726696792566285)
          ·
            refine ⟨200669417156522511297212357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 535118445750726696792566285 200669417156522511297212357)
            ·
              refine ⟨37625515716847970868227317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 200669417156522511297212357 37625515716847970868227317)
              ·
                refine ⟨3527392098454497268896311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37625515716847970868227317 3527392098454497268896311)
                ·
                  refine ⟨5291088147681745903344467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3527392098454497268896311 5291088147681745903344467)
                  ·
                    refine ⟨7936632221522618855016701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5291088147681745903344467 7936632221522618855016701)
                    ·
                      refine ⟨2976237083070982070631263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7936632221522618855016701 2976237083070982070631263)
                      ·
                        rfl

theorem cell23_5796201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 5, 1, 1, 3].length) (baseStart_5796201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796201 prefixEnd_5796201 := by exact prefixLift 5796201
  have htrace : WordTrace (prefixWord ++ tailWord_5796201) baseStart_5796201 baseEnd_5796201 := by
    simpa [prefixWord, tailWord_5796201, baseEnd_5796201] using wordTrace_append hprefix tailTrace_5796201
  have hstable : (prefixWord ++ tailWord_5796201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796201).length < 2 ^ (prefixWord ++ tailWord_5796201).sum := by decide
  have hdescent : baseEnd_5796201 < baseStart_5796201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796264 : List Nat := [2, 1, 6, 1, 1, 2, 10]
def baseStart_5796264 : Nat := 118140960795 + 5796264 * 2 ^ 59
def prefixEnd_5796264 : Nat := 4983230072969 + 3 ^ 40 * 5796264 * 2
def baseEnd_5796264 : Nat := 36744067066076732396833

theorem tailTrace_5796264 : CollatzResearch.WordTrace tailWord_5796264 prefixEnd_5796264 36744067066076732396833 := by
  unfold tailWord_5796264
  simp only [CollatzResearch.WordTrace]
  refine ⟨105703557936566462962253923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140938077248755283949671897 105703557936566462962253923)
  ·
    refine ⟨158555336904849694443380885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105703557936566462962253923 158555336904849694443380885)
    ·
      refine ⟨7432281417414829427033479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 158555336904849694443380885 7432281417414829427033479)
      ·
        refine ⟨11148422126122244140550219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7432281417414829427033479 11148422126122244140550219)
        ·
          refine ⟨16722633189183366210825329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11148422126122244140550219 16722633189183366210825329)
          ·
            refine ⟨12541974891887524658118997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16722633189183366210825329 12541974891887524658118997)
            ·
              refine ⟨36744067066076732396833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12541974891887524658118997 36744067066076732396833)
              ·
                rfl

theorem cell23_5796264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 10].length) (baseStart_5796264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796264 prefixEnd_5796264 := by exact prefixLift 5796264
  have htrace : WordTrace (prefixWord ++ tailWord_5796264) baseStart_5796264 baseEnd_5796264 := by
    simpa [prefixWord, tailWord_5796264, baseEnd_5796264] using wordTrace_append hprefix tailTrace_5796264
  have hstable : (prefixWord ++ tailWord_5796264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796264).length < 2 ^ (prefixWord ++ tailWord_5796264).sum := by decide
  have hdescent : baseEnd_5796264 < baseStart_5796264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796297 : List Nat := [1, 2, 1, 1, 2, 1, 4, 2, 2, 3, 4]
def baseStart_5796297 : Nat := 118140960795 + 5796297 * 2 ^ 59
def prefixEnd_5796297 : Nat := 4983230072969 + 3 ^ 40 * 5796297 * 2
def baseEnd_5796297 : Nat := 2976286377213813695030821

theorem tailTrace_5796297 : CollatzResearch.WordTrace tailWord_5796297 prefixEnd_5796297 2976286377213813695030821 := by
  unfold tailWord_5796297
  simp only [CollatzResearch.WordTrace]
  refine ⟨211408319482013372560459145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140938879654675581706972763 211408319482013372560459145)
  ·
    refine ⟨158556239611510029420344359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211408319482013372560459145 158556239611510029420344359)
    ·
      refine ⟨237834359417265044130516539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158556239611510029420344359 237834359417265044130516539)
      ·
        refine ⟨356751539125897566195774809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237834359417265044130516539 356751539125897566195774809)
        ·
          refine ⟨267563654344423174646831107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 356751539125897566195774809 267563654344423174646831107)
          ·
            refine ⟨401345481516634761970246661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267563654344423174646831107 401345481516634761970246661)
            ·
              refine ⟨75252277784369017869421249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 401345481516634761970246661 75252277784369017869421249)
              ·
                refine ⟨56439208338276763402065937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75252277784369017869421249 56439208338276763402065937)
                ·
                  refine ⟨42329406253707572551549453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56439208338276763402065937 42329406253707572551549453)
                  ·
                    refine ⟨15873527345140339706831045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42329406253707572551549453 15873527345140339706831045)
                    ·
                      refine ⟨2976286377213813695030821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15873527345140339706831045 2976286377213813695030821)
                      ·
                        rfl

theorem cell23_5796297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 3, 4].length) (baseStart_5796297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796297 prefixEnd_5796297 := by exact prefixLift 5796297
  have htrace : WordTrace (prefixWord ++ tailWord_5796297) baseStart_5796297 baseEnd_5796297 := by
    simpa [prefixWord, tailWord_5796297, baseEnd_5796297] using wordTrace_append hprefix tailTrace_5796297
  have hstable : (prefixWord ++ tailWord_5796297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796297).length < 2 ^ (prefixWord ++ tailWord_5796297).sum := by decide
  have hdescent : baseEnd_5796297 < baseStart_5796297 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796331 : List Nat := [1, 1, 1, 1, 2, 3, 3, 3, 4, 2, 2]
def baseStart_5796331 : Nat := 118140960795 + 5796331 * 2 ^ 59
def prefixEnd_5796331 : Nat := 4983230072969 + 3 ^ 40 * 5796331 * 2
def baseEnd_5796331 : Nat := 2976303835556066562005665

theorem tailTrace_5796331 : CollatzResearch.WordTrace tailWord_5796331 prefixEnd_5796331 2976303835556066562005665 := by
  unfold tailWord_5796331
  simp only [CollatzResearch.WordTrace]
  refine ⟨211409559563890196367196847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140939706375926797578131231 211409559563890196367196847)
  ·
    refine ⟨317114339345835294550795271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211409559563890196367196847 317114339345835294550795271)
    ·
      refine ⟨475671509018752941826192907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317114339345835294550795271 475671509018752941826192907)
      ·
        refine ⟨713507263528129412739289361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475671509018752941826192907 713507263528129412739289361)
        ·
          refine ⟨535130447646097059554467021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 713507263528129412739289361 535130447646097059554467021)
          ·
            refine ⟨200673917867286397332925133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 535130447646097059554467021 200673917867286397332925133)
            ·
              refine ⟨75252719200232398999846925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 200673917867286397332925133 75252719200232398999846925)
              ·
                refine ⟨28219769700087149624942597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75252719200232398999846925 28219769700087149624942597)
                ·
                  refine ⟨5291206818766340554676737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28219769700087149624942597 5291206818766340554676737)
                  ·
                    refine ⟨3968405114074755416007553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5291206818766340554676737 3968405114074755416007553)
                    ·
                      refine ⟨2976303835556066562005665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3968405114074755416007553 2976303835556066562005665)
                      ·
                        rfl

theorem cell23_5796331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 4, 2, 2].length) (baseStart_5796331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796331 prefixEnd_5796331 := by exact prefixLift 5796331
  have htrace : WordTrace (prefixWord ++ tailWord_5796331) baseStart_5796331 baseEnd_5796331 := by
    simpa [prefixWord, tailWord_5796331, baseEnd_5796331] using wordTrace_append hprefix tailTrace_5796331
  have hstable : (prefixWord ++ tailWord_5796331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796331).length < 2 ^ (prefixWord ++ tailWord_5796331).sum := by decide
  have hdescent : baseEnd_5796331 < baseStart_5796331 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796365 : List Nat := [1, 7, 1, 1, 1, 1, 1, 1, 3, 4, 2]
def baseStart_5796365 : Nat := 118140960795 + 5796365 * 2 ^ 59
def prefixEnd_5796365 : Nat := 4983230072969 + 3 ^ 40 * 5796365 * 2
def baseEnd_5796365 : Nat := 2976321293898319428980509

theorem tailTrace_5796365 : CollatzResearch.WordTrace tailWord_5796365 prefixEnd_5796365 2976321293898319428980509 := by
  unfold tailWord_5796365
  simp only [CollatzResearch.WordTrace]
  refine ⟨211410799645767020173934549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140940533097178013449289699 211410799645767020173934549)
  ·
    refine ⟨4954940616697664535326591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 211410799645767020173934549 4954940616697664535326591)
    ·
      refine ⟨7432410925046496802989887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4954940616697664535326591 7432410925046496802989887)
      ·
        refine ⟨11148616387569745204484831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7432410925046496802989887 11148616387569745204484831)
        ·
          refine ⟨16722924581354617806727247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11148616387569745204484831 16722924581354617806727247)
          ·
            refine ⟨25084386872031926710090871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16722924581354617806727247 25084386872031926710090871)
            ·
              refine ⟨37626580308047890065136307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25084386872031926710090871 37626580308047890065136307)
              ·
                refine ⟨56439870462071835097704461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37626580308047890065136307 56439870462071835097704461)
                ·
                  refine ⟨21164951423276938161639173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56439870462071835097704461 21164951423276938161639173)
                  ·
                    refine ⟨3968428391864425905307345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21164951423276938161639173 3968428391864425905307345)
                    ·
                      refine ⟨2976321293898319428980509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3968428391864425905307345 2976321293898319428980509)
                      ·
                        rfl

theorem cell23_5796365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_5796365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796365 prefixEnd_5796365 := by exact prefixLift 5796365
  have htrace : WordTrace (prefixWord ++ tailWord_5796365) baseStart_5796365 baseEnd_5796365 := by
    simpa [prefixWord, tailWord_5796365, baseEnd_5796365] using wordTrace_append hprefix tailTrace_5796365
  have hstable : (prefixWord ++ tailWord_5796365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796365).length < 2 ^ (prefixWord ++ tailWord_5796365).sum := by decide
  have hdescent : baseEnd_5796365 < baseStart_5796365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796377 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 3, 1, 7]
def baseStart_5796377 : Nat := 118140960795 + 5796377 * 2 ^ 59
def prefixEnd_5796377 : Nat := 4983230072969 + 3 ^ 40 * 5796377 * 2
def baseEnd_5796377 : Nat := 2976327455666173382030453

theorem tailTrace_5796377 : CollatzResearch.WordTrace tailWord_5796377 prefixEnd_5796377 2976327455666173382030453 := by
  unfold tailWord_5796377
  simp only [CollatzResearch.WordTrace]
  refine ⟨211411237321723546223371385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140940824881149030815580923 211411237321723546223371385)
  ·
    refine ⟨158558427991292659667528539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211411237321723546223371385 158558427991292659667528539)
    ·
      refine ⟨237837641986938989501292809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158558427991292659667528539 237837641986938989501292809)
      ·
        refine ⟨178378231490204242125969607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237837641986938989501292809 178378231490204242125969607)
        ·
          refine ⟨267567347235306363188954411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178378231490204242125969607 267567347235306363188954411)
          ·
            refine ⟨401351020852959544783431617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267567347235306363188954411 401351020852959544783431617)
            ·
              refine ⟨301013265639719658587573713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 401351020852959544783431617 301013265639719658587573713)
              ·
                refine ⟨225759949229789743940680285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 301013265639719658587573713 225759949229789743940680285)
                ·
                  refine ⟨84659980961171153977755107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 225759949229789743940680285 84659980961171153977755107)
                  ·
                    refine ⟨126989971441756730966632661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 84659980961171153977755107 126989971441756730966632661)
                    ·
                      refine ⟨2976327455666173382030453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 126989971441756730966632661 2976327455666173382030453)
                      ·
                        rfl

theorem cell23_5796377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 1, 7].length) (baseStart_5796377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796377 prefixEnd_5796377 := by exact prefixLift 5796377
  have htrace : WordTrace (prefixWord ++ tailWord_5796377) baseStart_5796377 baseEnd_5796377 := by
    simpa [prefixWord, tailWord_5796377, baseEnd_5796377] using wordTrace_append hprefix tailTrace_5796377
  have hstable : (prefixWord ++ tailWord_5796377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796377).length < 2 ^ (prefixWord ++ tailWord_5796377).sum := by decide
  have hdescent : baseEnd_5796377 < baseStart_5796377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796398 : List Nat := [4, 1, 3, 1, 3, 1, 1, 1, 2, 3, 3]
def baseStart_5796398 : Nat := 118140960795 + 5796398 * 2 ^ 59
def prefixEnd_5796398 : Nat := 4983230072969 + 3 ^ 40 * 5796398 * 2
def baseEnd_5796398 : Nat := 2976338238759917799867857

theorem tailTrace_5796398 : CollatzResearch.WordTrace tailWord_5796398 prefixEnd_5796398 2976338238759917799867857 := by
  unfold tailWord_5796398
  simp only [CollatzResearch.WordTrace]
  refine ⟨26426500406830933351235731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140941335503098311206590565 26426500406830933351235731)
  ·
    refine ⟨39639750610246400026853597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26426500406830933351235731 39639750610246400026853597)
    ·
      refine ⟨14864906478842400010070099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39639750610246400026853597 14864906478842400010070099)
      ·
        refine ⟨22297359718263600015105149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14864906478842400010070099 22297359718263600015105149)
        ·
          refine ⟨8361509894348850005664431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22297359718263600015105149 8361509894348850005664431)
          ·
            refine ⟨12542264841523275008496647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8361509894348850005664431 12542264841523275008496647)
            ·
              refine ⟨18813397262284912512744971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12542264841523275008496647 18813397262284912512744971)
              ·
                refine ⟨28220095893427368769117457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18813397262284912512744971 28220095893427368769117457)
                ·
                  refine ⟨21165071920070526576838093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28220095893427368769117457 21165071920070526576838093)
                  ·
                    refine ⟨7936901970026447466314285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21165071920070526576838093 7936901970026447466314285)
                    ·
                      refine ⟨2976338238759917799867857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7936901970026447466314285 2976338238759917799867857)
                      ·
                        rfl

theorem cell23_5796398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_5796398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796398 prefixEnd_5796398 := by exact prefixLift 5796398
  have htrace : WordTrace (prefixWord ++ tailWord_5796398) baseStart_5796398 baseEnd_5796398 := by
    simpa [prefixWord, tailWord_5796398, baseEnd_5796398] using wordTrace_append hprefix tailTrace_5796398
  have hstable : (prefixWord ++ tailWord_5796398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796398).length < 2 ^ (prefixWord ++ tailWord_5796398).sum := by decide
  have hdescent : baseEnd_5796398 < baseStart_5796398 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796421 : List Nat := [1, 3, 1, 1, 1, 5, 3, 1, 2, 1, 4]
def baseStart_5796421 : Nat := 118140960795 + 5796421 * 2 ^ 59
def prefixEnd_5796421 : Nat := 4983230072969 + 3 ^ 40 * 5796421 * 2
def baseEnd_5796421 : Nat := 2976350048814971209880251

theorem tailTrace_5796421 : CollatzResearch.WordTrace tailWord_5796421 prefixEnd_5796421 2976350048814971209880251 := by
  unfold tailWord_5796421
  simp only [CollatzResearch.WordTrace]
  refine ⟨211412842133564141737973117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140941894755709427825315411 211412842133564141737973117)
  ·
    refine ⟨79279815800086553151739919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211412842133564141737973117 79279815800086553151739919)
    ·
      refine ⟨118919723700129829727609879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79279815800086553151739919 118919723700129829727609879)
      ·
        refine ⟨178379585550194744591414819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118919723700129829727609879 178379585550194744591414819)
        ·
          refine ⟨267569378325292116887122229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178379585550194744591414819 267569378325292116887122229)
          ·
            refine ⟨25084629217996135958167709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 267569378325292116887122229 25084629217996135958167709)
            ·
              refine ⟨9406735956748550984312891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25084629217996135958167709 9406735956748550984312891)
              ·
                refine ⟨14110103935122826476469337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9406735956748550984312891 14110103935122826476469337)
                ·
                  refine ⟨10582577951342119857352003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14110103935122826476469337 10582577951342119857352003)
                  ·
                    refine ⟨15873866927013179786028005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10582577951342119857352003 15873866927013179786028005)
                    ·
                      refine ⟨2976350048814971209880251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15873866927013179786028005 2976350048814971209880251)
                      ·
                        rfl

theorem cell23_5796421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 2, 1, 4].length) (baseStart_5796421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796421 prefixEnd_5796421 := by exact prefixLift 5796421
  have htrace : WordTrace (prefixWord ++ tailWord_5796421) baseStart_5796421 baseEnd_5796421 := by
    simpa [prefixWord, tailWord_5796421, baseEnd_5796421] using wordTrace_append hprefix tailTrace_5796421
  have hstable : (prefixWord ++ tailWord_5796421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796421).length < 2 ^ (prefixWord ++ tailWord_5796421).sum := by decide
  have hdescent : baseEnd_5796421 < baseStart_5796421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796434 : List Nat := [3, 2, 2, 1, 2, 1, 1, 1, 1, 3, 6]
def baseStart_5796434 : Nat := 118140960795 + 5796434 * 2 ^ 59
def prefixEnd_5796434 : Nat := 4983230072969 + 3 ^ 40 * 5796434 * 2
def baseEnd_5796434 : Nat := 2976356724063479659017691

theorem tailTrace_5796434 : CollatzResearch.WordTrace tailWord_5796434 prefixEnd_5796434 2976356724063479659017691 := by
  unfold tailWord_5796434
  simp only [CollatzResearch.WordTrace]
  refine ⟨52853329070629261239549089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140942210855011363305464237 52853329070629261239549089)
  ·
    refine ⟨39639996802971945929661817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52853329070629261239549089 39639996802971945929661817)
    ·
      refine ⟨29729997602228959447246363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39639996802971945929661817 29729997602228959447246363)
      ·
        refine ⟨44594996403343439170869545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29729997602228959447246363 44594996403343439170869545)
        ·
          refine ⟨33446247302507579378152159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44594996403343439170869545 33446247302507579378152159)
          ·
            refine ⟨50169370953761369067228239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33446247302507579378152159 50169370953761369067228239)
            ·
              refine ⟨75254056430642053600842359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50169370953761369067228239 75254056430642053600842359)
              ·
                refine ⟨112881084645963080401263539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75254056430642053600842359 112881084645963080401263539)
                ·
                  refine ⟨169321626968944620601895309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112881084645963080401263539 169321626968944620601895309)
                  ·
                    refine ⟨63495610113354232725710741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 169321626968944620601895309 63495610113354232725710741)
                    ·
                      refine ⟨2976356724063479659017691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63495610113354232725710741 2976356724063479659017691)
                      ·
                        rfl

theorem cell23_5796434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_5796434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796434 prefixEnd_5796434 := by exact prefixLift 5796434
  have htrace : WordTrace (prefixWord ++ tailWord_5796434) baseStart_5796434 baseEnd_5796434 := by
    simpa [prefixWord, tailWord_5796434, baseEnd_5796434] using wordTrace_append hprefix tailTrace_5796434
  have hstable : (prefixWord ++ tailWord_5796434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796434).length < 2 ^ (prefixWord ++ tailWord_5796434).sum := by decide
  have hdescent : baseEnd_5796434 < baseStart_5796434 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796448 : List Nat := [2, 1, 1, 3, 2, 1, 4, 4, 1, 4]
def baseStart_5796448 : Nat := 118140960795 + 5796448 * 2 ^ 59
def prefixEnd_5796448 : Nat := 4983230072969 + 3 ^ 40 * 5796448 * 2
def baseEnd_5796448 : Nat := 992121304264214201414209

theorem tailTrace_5796448 : CollatzResearch.WordTrace tailWord_5796448 prefixEnd_5796448 992121304264214201414209 := by
  unfold tailWord_5796448
  simp only [CollatzResearch.WordTrace]
  refine ⟨105706913452233162674602999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140942551269644216899470665 105706913452233162674602999)
  ·
    refine ⟨158560370178349744011904499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105706913452233162674602999 158560370178349744011904499)
    ·
      refine ⟨237840555267524616017856749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158560370178349744011904499 237840555267524616017856749)
      ·
        refine ⟨89190208225321731006696281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 237840555267524616017856749 89190208225321731006696281)
        ·
          refine ⟨66892656168991298255022211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89190208225321731006696281 66892656168991298255022211)
          ·
            refine ⟨100338984253486947382533317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66892656168991298255022211 100338984253486947382533317)
            ·
              refine ⟨18813559547528802634224997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100338984253486947382533317 18813559547528802634224997)
              ·
                refine ⟨3527542415161650493917187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18813559547528802634224997 3527542415161650493917187)
                ·
                  refine ⟨5291313622742475740875781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3527542415161650493917187 5291313622742475740875781)
                  ·
                    refine ⟨992121304264214201414209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5291313622742475740875781 992121304264214201414209)
                    ·
                      rfl

theorem cell23_5796448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 4, 1, 4].length) (baseStart_5796448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796448 prefixEnd_5796448 := by exact prefixLift 5796448
  have htrace : WordTrace (prefixWord ++ tailWord_5796448) baseStart_5796448 baseEnd_5796448 := by
    simpa [prefixWord, tailWord_5796448, baseEnd_5796448] using wordTrace_append hprefix tailTrace_5796448
  have hstable : (prefixWord ++ tailWord_5796448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796448).length < 2 ^ (prefixWord ++ tailWord_5796448).sum := by decide
  have hdescent : baseEnd_5796448 < baseStart_5796448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796474 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 7, 5]
def baseStart_5796474 : Nat := 118140960795 + 5796474 * 2 ^ 59
def prefixEnd_5796474 : Nat := 4983230072969 + 3 ^ 40 * 5796474 * 2
def baseEnd_5796474 : Nat := 992125754429886500839169

theorem tailTrace_5796474 : CollatzResearch.WordTrace tailWord_5796474 prefixEnd_5796474 992125754429886500839169 := by
  unfold tailWord_5796474
  simp only [CollatzResearch.WordTrace]
  refine ⟨52853693800593032947413119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140943183468248087859768317 52853693800593032947413119)
  ·
    refine ⟨79280540700889549421119679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52853693800593032947413119 79280540700889549421119679)
    ·
      refine ⟨118920811051334324131679519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79280540700889549421119679 118920811051334324131679519)
      ·
        refine ⟨178381216577001486197519279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118920811051334324131679519 178381216577001486197519279)
        ·
          refine ⟨267571824865502229296278919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178381216577001486197519279 267571824865502229296278919)
          ·
            refine ⟨401357737298253343944418379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267571824865502229296278919 401357737298253343944418379)
            ·
              refine ⟨602036605947380015916627569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 401357737298253343944418379 602036605947380015916627569)
              ·
                refine ⟨451527454460535011937470677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 602036605947380015916627569 451527454460535011937470677)
                ·
                  refine ⟨10582674713918789342284469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 451527454460535011937470677 10582674713918789342284469)
                  ·
                    refine ⟨992125754429886500839169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10582674713918789342284469 992125754429886500839169)
                    ·
                      rfl

theorem cell23_5796474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 7, 5].length) (baseStart_5796474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796474 prefixEnd_5796474 := by exact prefixLift 5796474
  have htrace : WordTrace (prefixWord ++ tailWord_5796474) baseStart_5796474 baseEnd_5796474 := by
    simpa [prefixWord, tailWord_5796474, baseEnd_5796474] using wordTrace_append hprefix tailTrace_5796474
  have hstable : (prefixWord ++ tailWord_5796474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796474).length < 2 ^ (prefixWord ++ tailWord_5796474).sum := by decide
  have hdescent : baseEnd_5796474 < baseStart_5796474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796525 : List Nat := [1, 5, 2, 1, 1, 4, 1, 2, 1, 5]
def baseStart_5796525 : Nat := 118140960795 + 5796525 * 2 ^ 59
def prefixEnd_5796525 : Nat := 4983230072969 + 3 ^ 40 * 5796525 * 2
def baseEnd_5796525 : Nat := 992134483601012934326591

theorem tailTrace_5796525 : CollatzResearch.WordTrace tailWord_5796525 prefixEnd_5796525 992134483601012934326591 := by
  unfold tailWord_5796525
  simp only [CollatzResearch.WordTrace]
  refine ⟨211416635325187367499759029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140944423550124911666506019 211416635325187367499759029)
  ·
    refine ⟨19820309561736315703102409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 211416635325187367499759029 19820309561736315703102409)
    ·
      refine ⟨14865232171302236777326807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19820309561736315703102409 14865232171302236777326807)
      ·
        refine ⟨22297848256953355165990211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14865232171302236777326807 22297848256953355165990211)
        ·
          refine ⟨33446772385430032748985317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22297848256953355165990211 33446772385430032748985317)
          ·
            refine ⟨6271269822268131140434747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33446772385430032748985317 6271269822268131140434747)
            ·
              refine ⟨9406904733402196710652121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6271269822268131140434747 9406904733402196710652121)
              ·
                refine ⟨7055178550051647532989091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9406904733402196710652121 7055178550051647532989091)
                ·
                  refine ⟨10582767825077471299483637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7055178550051647532989091 10582767825077471299483637)
                  ·
                    refine ⟨992134483601012934326591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10582767825077471299483637 992134483601012934326591)
                    ·
                      rfl

theorem cell23_5796525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_5796525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796525 prefixEnd_5796525 := by exact prefixLift 5796525
  have htrace : WordTrace (prefixWord ++ tailWord_5796525) baseStart_5796525 baseEnd_5796525 := by
    simpa [prefixWord, tailWord_5796525, baseEnd_5796525] using wordTrace_append hprefix tailTrace_5796525
  have hstable : (prefixWord ++ tailWord_5796525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796525).length < 2 ^ (prefixWord ++ tailWord_5796525).sum := by decide
  have hdescent : baseEnd_5796525 < baseStart_5796525 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796528 : List Nat := [2, 1, 1, 1, 2, 1, 3, 3, 5, 2, 2]
def baseStart_5796528 : Nat := 118140960795 + 5796528 * 2 ^ 59
def prefixEnd_5796528 : Nat := 4983230072969 + 3 ^ 40 * 5796528 * 2
def baseEnd_5796528 : Nat := 2976404991245002291242259

theorem tailTrace_5796528 : CollatzResearch.WordTrace tailWord_5796528 prefixEnd_5796528 2976404991245002291242259 := by
  unfold tailWord_5796528
  simp only [CollatzResearch.WordTrace]
  refine ⟨105708372372088249506059119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140944496496117666008078825 105708372372088249506059119)
  ·
    refine ⟨158562558558132374259088679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105708372372088249506059119 158562558558132374259088679)
    ·
      refine ⟨237843837837198561388633019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158562558558132374259088679 237843837837198561388633019)
      ·
        refine ⟨356765756755797842082949529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237843837837198561388633019 356765756755797842082949529)
        ·
          refine ⟨267574317566848381562212147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 356765756755797842082949529 267574317566848381562212147)
          ·
            refine ⟨401361476350272572343318221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267574317566848381562212147 401361476350272572343318221)
            ·
              refine ⟨150510553631352214628744333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 401361476350272572343318221 150510553631352214628744333)
              ·
                refine ⟨56441457611757080485779125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150510553631352214628744333 56441457611757080485779125)
                ·
                  refine ⟨5291386651102226295541793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56441457611757080485779125 5291386651102226295541793)
                  ·
                    refine ⟨3968539988326669721656345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5291386651102226295541793 3968539988326669721656345)
                    ·
                      refine ⟨2976404991245002291242259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3968539988326669721656345 2976404991245002291242259)
                      ·
                        rfl

theorem cell23_5796528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 5, 2, 2].length) (baseStart_5796528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796528 prefixEnd_5796528 := by exact prefixLift 5796528
  have htrace : WordTrace (prefixWord ++ tailWord_5796528) baseStart_5796528 baseEnd_5796528 := by
    simpa [prefixWord, tailWord_5796528, baseEnd_5796528] using wordTrace_append hprefix tailTrace_5796528
  have hstable : (prefixWord ++ tailWord_5796528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796528).length < 2 ^ (prefixWord ++ tailWord_5796528).sum := by decide
  have hdescent : baseEnd_5796528 < baseStart_5796528 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796541 : List Nat := [1, 4, 1, 2, 1, 3, 1, 1, 3, 2, 4]
def baseStart_5796541 : Nat := 118140960795 + 5796541 * 2 ^ 59
def prefixEnd_5796541 : Nat := 4983230072969 + 3 ^ 40 * 5796541 * 2
def baseEnd_5796541 : Nat := 2976411666493510740379699

theorem tailTrace_5796541 : CollatzResearch.WordTrace tailWord_5796541 prefixEnd_5796541 2976411666493510740379699 := by
  unfold tailWord_5796541
  simp only [CollatzResearch.WordTrace]
  refine ⟨211417218893129402232341477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140944812595419601488227651 211417218893129402232341477)
  ·
    refine ⟨39640728542461762918564027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 211417218893129402232341477 39640728542461762918564027)
    ·
      refine ⟨59461092813692644377846041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39640728542461762918564027 59461092813692644377846041)
      ·
        refine ⟨44595819610269483283384531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59461092813692644377846041 44595819610269483283384531)
        ·
          refine ⟨66893729415404224925076797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44595819610269483283384531 66893729415404224925076797)
          ·
            refine ⟨25085148530776584346903799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66893729415404224925076797 25085148530776584346903799)
            ·
              refine ⟨37627722796164876520355699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25085148530776584346903799 37627722796164876520355699)
              ·
                refine ⟨56441584194247314780533549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37627722796164876520355699 56441584194247314780533549)
                ·
                  refine ⟨21165594072842743042700081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56441584194247314780533549 21165594072842743042700081)
                  ·
                    refine ⟨15874195554632057282025061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21165594072842743042700081 15874195554632057282025061)
                    ·
                      refine ⟨2976411666493510740379699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15874195554632057282025061 2976411666493510740379699)
                      ·
                        rfl

theorem cell23_5796541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_5796541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796541 prefixEnd_5796541 := by exact prefixLift 5796541
  have htrace : WordTrace (prefixWord ++ tailWord_5796541) baseStart_5796541 baseEnd_5796541 := by
    simpa [prefixWord, tailWord_5796541, baseEnd_5796541] using wordTrace_append hprefix tailTrace_5796541
  have hstable : (prefixWord ++ tailWord_5796541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796541).length < 2 ^ (prefixWord ++ tailWord_5796541).sum := by decide
  have hdescent : baseEnd_5796541 < baseStart_5796541 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796548 : List Nat := [2, 3, 3, 1, 1, 2, 3, 1, 1, 1, 5]
def baseStart_5796548 : Nat := 118140960795 + 5796548 * 2 ^ 59
def prefixEnd_5796548 : Nat := 4983230072969 + 3 ^ 40 * 5796548 * 2
def baseEnd_5796548 : Nat := 2976415260858092212992167

theorem tailTrace_5796548 : CollatzResearch.WordTrace tailWord_5796548 prefixEnd_5796548 2976415260858092212992167 := by
  unfold tailWord_5796548
  simp only [CollatzResearch.WordTrace]
  refine ⟨105708737102052021213923149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140944982802736028285230865 105708737102052021213923149)
  ·
    refine ⟨39640776413269507955221181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105708737102052021213923149 39640776413269507955221181)
    ·
      refine ⟨14865291154976065483207943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39640776413269507955221181 14865291154976065483207943)
      ·
        refine ⟨22297936732464098224811915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14865291154976065483207943 22297936732464098224811915)
        ·
          refine ⟨33446905098696147337217873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22297936732464098224811915 33446905098696147337217873)
          ·
            refine ⟨25085178824022110502913405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33446905098696147337217873 25085178824022110502913405)
            ·
              refine ⟨9406942059008291438592527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25085178824022110502913405 9406942059008291438592527)
              ·
                refine ⟨14110413088512437157888791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9406942059008291438592527 14110413088512437157888791)
                ·
                  refine ⟨21165619632768655736833187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14110413088512437157888791 21165619632768655736833187)
                  ·
                    refine ⟨31748429449152983605249781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21165619632768655736833187 31748429449152983605249781)
                    ·
                      refine ⟨2976415260858092212992167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31748429449152983605249781 2976415260858092212992167)
                      ·
                        rfl

theorem cell23_5796548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_5796548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796548 prefixEnd_5796548 := by exact prefixLift 5796548
  have htrace : WordTrace (prefixWord ++ tailWord_5796548) baseStart_5796548 baseEnd_5796548 := by
    simpa [prefixWord, tailWord_5796548, baseEnd_5796548] using wordTrace_append hprefix tailTrace_5796548
  have hstable : (prefixWord ++ tailWord_5796548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796548).length < 2 ^ (prefixWord ++ tailWord_5796548).sum := by decide
  have hdescent : baseEnd_5796548 < baseStart_5796548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796561 : List Nat := [1, 2, 2, 1, 2, 3, 1, 2, 3, 3, 3]
def baseStart_5796561 : Nat := 118140960795 + 5796561 * 2 ^ 59
def prefixEnd_5796561 : Nat := 4983230072969 + 3 ^ 40 * 5796561 * 2
def baseEnd_5796561 : Nat := 2976421936106600662129607

theorem tailTrace_5796561 : CollatzResearch.WordTrace tailWord_5796561 prefixEnd_5796561 2976421936106600662129607 := by
  unfold tailWord_5796561
  simp only [CollatzResearch.WordTrace]
  refine ⟨211417948353056945648069537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140945298902037963765379691 211417948353056945648069537)
  ·
    refine ⟨158563461264792709236052153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211417948353056945648069537 158563461264792709236052153)
    ·
      refine ⟨118922595948594531927039115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158563461264792709236052153 118922595948594531927039115)
      ·
        refine ⟨178383893922891797890558673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118922595948594531927039115 178383893922891797890558673)
        ·
          refine ⟨133787920442168848417919005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178383893922891797890558673 133787920442168848417919005)
          ·
            refine ⟨50170470165813318156719627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133787920442168848417919005 50170470165813318156719627)
            ·
              refine ⟨75255705248719977235079441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50170470165813318156719627 75255705248719977235079441)
              ·
                refine ⟨56441778936539982926309581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75255705248719977235079441 56441778936539982926309581)
                ·
                  refine ⟨21165667101202493597366093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56441778936539982926309581 21165667101202493597366093)
                  ·
                    refine ⟨7937125162950935099012285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21165667101202493597366093 7937125162950935099012285)
                    ·
                      refine ⟨2976421936106600662129607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7937125162950935099012285 2976421936106600662129607)
                      ·
                        rfl

theorem cell23_5796561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 3, 3].length) (baseStart_5796561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796561 prefixEnd_5796561 := by exact prefixLift 5796561
  have htrace : WordTrace (prefixWord ++ tailWord_5796561) baseStart_5796561 baseEnd_5796561 := by
    simpa [prefixWord, tailWord_5796561, baseEnd_5796561] using wordTrace_append hprefix tailTrace_5796561
  have hstable : (prefixWord ++ tailWord_5796561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796561).length < 2 ^ (prefixWord ++ tailWord_5796561).sum := by decide
  have hdescent : baseEnd_5796561 < baseStart_5796561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796596 : List Nat := [2, 6, 1, 1, 2, 2, 2, 1, 1, 1, 4]
def baseStart_5796596 : Nat := 118140960795 + 5796596 * 2 ^ 59
def prefixEnd_5796596 : Nat := 4983230072969 + 3 ^ 40 * 5796596 * 2
def baseEnd_5796596 : Nat := 2976439907929508025191947

theorem tailTrace_5796596 : CollatzResearch.WordTrace tailWord_5796596 prefixEnd_5796596 2976439907929508025191947 := by
  unfold tailWord_5796596
  simp only [CollatzResearch.WordTrace]
  refine ⟨105709612453965073312796821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140946149938620097750395761 105709612453965073312796821)
  ·
    refine ⟨4955138083779612811537351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 105709612453965073312796821 4955138083779612811537351)
    ·
      refine ⟨7432707125669419217306027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4955138083779612811537351 7432707125669419217306027)
      ·
        refine ⟨11149060688504128825959041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7432707125669419217306027 11149060688504128825959041)
        ·
          refine ⟨8361795516378096619469281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11149060688504128825959041 8361795516378096619469281)
          ·
            refine ⟨6271346637283572464601961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8361795516378096619469281 6271346637283572464601961)
            ·
              refine ⟨4703509977962679348451471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6271346637283572464601961 4703509977962679348451471)
              ·
                refine ⟨7055264966944019022677207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4703509977962679348451471 7055264966944019022677207)
                ·
                  refine ⟨10582897450416028534015811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7055264966944019022677207 10582897450416028534015811)
                  ·
                    refine ⟨15874346175624042801023717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10582897450416028534015811 15874346175624042801023717)
                    ·
                      refine ⟨2976439907929508025191947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15874346175624042801023717 2976439907929508025191947)
                      ·
                        rfl

theorem cell23_5796596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_5796596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796596 prefixEnd_5796596 := by exact prefixLift 5796596
  have htrace : WordTrace (prefixWord ++ tailWord_5796596) baseStart_5796596 baseEnd_5796596 := by
    simpa [prefixWord, tailWord_5796596, baseEnd_5796596] using wordTrace_append hprefix tailTrace_5796596
  have hstable : (prefixWord ++ tailWord_5796596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796596).length < 2 ^ (prefixWord ++ tailWord_5796596).sum := by decide
  have hdescent : baseEnd_5796596 < baseStart_5796596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796605 : List Nat := [1, 4, 1, 1, 1, 1, 5, 3, 1, 3, 2]
def baseStart_5796605 : Nat := 118140960795 + 5796605 * 2 ^ 59
def prefixEnd_5796605 : Nat := 4983230072969 + 3 ^ 40 * 5796605 * 2
def baseEnd_5796605 : Nat := 2976444529255398489979405

theorem tailTrace_5796605 : CollatzResearch.WordTrace tailWord_5796605 prefixEnd_5796605 2976444529255398489979405 := by
  unfold tailWord_5796605
  simp only [CollatzResearch.WordTrace]
  refine ⟨211419553164897541162671269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140946368776598360775114179 211419553164897541162671269)
  ·
    refine ⟨39641166218418288968000863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 211419553164897541162671269 39641166218418288968000863)
    ·
      refine ⟨59461749327627433452001295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39641166218418288968000863 59461749327627433452001295)
      ·
        refine ⟨89192623991441150178001943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59461749327627433452001295 89192623991441150178001943)
        ·
          refine ⟨133788935987161725267002915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89192623991441150178001943 133788935987161725267002915)
          ·
            refine ⟨200683403980742587900504373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133788935987161725267002915 200683403980742587900504373)
            ·
              refine ⟨18814069123194617615672285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 200683403980742587900504373 18814069123194617615672285)
              ·
                refine ⟨7055275921197981605877107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18814069123194617615672285 7055275921197981605877107)
                ·
                  refine ⟨10582913881796972408815661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7055275921197981605877107 10582913881796972408815661)
                  ·
                    refine ⟨3968592705673864653305873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10582913881796972408815661 3968592705673864653305873)
                    ·
                      refine ⟨2976444529255398489979405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3968592705673864653305873 2976444529255398489979405)
                      ·
                        rfl

theorem cell23_5796605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 3, 1, 3, 2].length) (baseStart_5796605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796605 prefixEnd_5796605 := by exact prefixLift 5796605
  have htrace : WordTrace (prefixWord ++ tailWord_5796605) baseStart_5796605 baseEnd_5796605 := by
    simpa [prefixWord, tailWord_5796605, baseEnd_5796605] using wordTrace_append hprefix tailTrace_5796605
  have hstable : (prefixWord ++ tailWord_5796605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796605).length < 2 ^ (prefixWord ++ tailWord_5796605).sum := by decide
  have hdescent : baseEnd_5796605 < baseStart_5796605 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796641 : List Nat := [1, 2, 3, 2, 1, 2, 1, 4, 7]
def baseStart_5796641 : Nat := 118140960795 + 5796641 * 2 ^ 59
def prefixEnd_5796641 : Nat := 4983230072969 + 3 ^ 40 * 5796641 * 2
def baseEnd_5796641 : Nat := 330718112728773372125471

theorem tailTrace_5796641 : CollatzResearch.WordTrace tailWord_5796641 prefixEnd_5796641 330718112728773372125471 := by
  unfold tailWord_5796641
  simp only [CollatzResearch.WordTrace]
  refine ⟨211420866192767119310981777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140947244128511412873987851 211420866192767119310981777)
  ·
    refine ⟨158565649644575339483236333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211420866192767119310981777 158565649644575339483236333)
    ·
      refine ⟨59462118616715752306213625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158565649644575339483236333 59462118616715752306213625)
      ·
        refine ⟨44596588962536814229660219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59462118616715752306213625 44596588962536814229660219)
        ·
          refine ⟨66894883443805221344490329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44596588962536814229660219 66894883443805221344490329)
          ·
            refine ⟨50171162582853916008367747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66894883443805221344490329 50171162582853916008367747)
            ·
              refine ⟨75256743874280874012551621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50171162582853916008367747 75256743874280874012551621)
              ·
                refine ⟨14110639476427663877353429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75256743874280874012551621 14110639476427663877353429)
                ·
                  refine ⟨330718112728773372125471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14110639476427663877353429 330718112728773372125471)
                  ·
                    rfl

theorem cell23_5796641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 7].length) (baseStart_5796641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796641 prefixEnd_5796641 := by exact prefixLift 5796641
  have htrace : WordTrace (prefixWord ++ tailWord_5796641) baseStart_5796641 baseEnd_5796641 := by
    simpa [prefixWord, tailWord_5796641, baseEnd_5796641] using wordTrace_append hprefix tailTrace_5796641
  have hstable : (prefixWord ++ tailWord_5796641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796641).length < 2 ^ (prefixWord ++ tailWord_5796641).sum := by decide
  have hdescent : baseEnd_5796641 < baseStart_5796641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796651 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 3, 5, 3]
def baseStart_5796651 : Nat := 118140960795 + 5796651 * 2 ^ 59
def prefixEnd_5796651 : Nat := 4983230072969 + 3 ^ 40 * 5796651 * 2
def baseEnd_5796651 : Nat := 2976468149365505310004193

theorem tailTrace_5796651 : CollatzResearch.WordTrace tailWord_5796651 prefixEnd_5796651 2976468149365505310004193 := by
  unfold tailWord_5796651
  simp only [CollatzResearch.WordTrace]
  refine ⟨211421230922730891018845807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140947487281820594012563871 211421230922730891018845807)
  ·
    refine ⟨317131846384096336528268711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211421230922730891018845807 317131846384096336528268711)
    ·
      refine ⟨475697769576144504792403067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317131846384096336528268711 475697769576144504792403067)
      ·
        refine ⟨713546654364216757188604601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475697769576144504792403067 713546654364216757188604601)
        ·
          refine ⟨535159990773162567891453451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 713546654364216757188604601 535159990773162567891453451)
          ·
            refine ⟨802739986159743851837180177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 535159990773162567891453451 802739986159743851837180177)
            ·
              refine ⟨602054989619807888877885133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 802739986159743851837180177 602054989619807888877885133)
              ·
                refine ⟨225770621107427958329206925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 602054989619807888877885133 225770621107427958329206925)
                ·
                  refine ⟨84663982915285484373452597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 225770621107427958329206925 84663982915285484373452597)
                  ·
                    refine ⟨7937248398308014160011181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 84663982915285484373452597 7937248398308014160011181)
                    ·
                      refine ⟨2976468149365505310004193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7937248398308014160011181 2976468149365505310004193)
                      ·
                        rfl

theorem cell23_5796651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 5, 3].length) (baseStart_5796651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796651 prefixEnd_5796651 := by exact prefixLift 5796651
  have htrace : WordTrace (prefixWord ++ tailWord_5796651) baseStart_5796651 baseEnd_5796651 := by
    simpa [prefixWord, tailWord_5796651, baseEnd_5796651] using wordTrace_append hprefix tailTrace_5796651
  have hstable : (prefixWord ++ tailWord_5796651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796651).length < 2 ^ (prefixWord ++ tailWord_5796651).sum := by decide
  have hdescent : baseEnd_5796651 < baseStart_5796651 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796675 : List Nat := [1, 1, 1, 3, 1, 4, 5, 2, 5]
def baseStart_5796675 : Nat := 118140960795 + 5796675 * 2 ^ 59
def prefixEnd_5796675 : Nat := 4983230072969 + 3 ^ 40 * 5796675 * 2
def baseEnd_5796675 : Nat := 330720052544579246233787

theorem tailTrace_5796675 : CollatzResearch.WordTrace tailWord_5796675 prefixEnd_5796675 330720052544579246233787 := by
  unfold tailWord_5796675
  simp only [CollatzResearch.WordTrace]
  refine ⟨211422106274643943117719479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140948070849762628745146319 211422106274643943117719479)
  ·
    refine ⟨317133159411965914676579219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211422106274643943117719479 317133159411965914676579219)
    ·
      refine ⟨475699739117948872014868829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317133159411965914676579219 475699739117948872014868829)
      ·
        refine ⟨178387402169230827005575811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 475699739117948872014868829 178387402169230827005575811)
        ·
          refine ⟨267581103253846240508363717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178387402169230827005575811 267581103253846240508363717)
          ·
            refine ⟨50171456860096170095318197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 267581103253846240508363717 50171456860096170095318197)
            ·
              refine ⟨4703574080634015946436081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50171456860096170095318197 4703574080634015946436081)
              ·
                refine ⟨3527680560475511959827061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4703574080634015946436081 3527680560475511959827061)
                ·
                  refine ⟨330720052544579246233787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3527680560475511959827061 330720052544579246233787)
                  ·
                    rfl

theorem cell23_5796675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 2, 5].length) (baseStart_5796675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796675 prefixEnd_5796675 := by exact prefixLift 5796675
  have htrace : WordTrace (prefixWord ++ tailWord_5796675) baseStart_5796675 baseEnd_5796675 := by
    simpa [prefixWord, tailWord_5796675, baseEnd_5796675] using wordTrace_append hprefix tailTrace_5796675
  have hstable : (prefixWord ++ tailWord_5796675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796675).length < 2 ^ (prefixWord ++ tailWord_5796675).sum := by decide
  have hdescent : baseEnd_5796675 < baseStart_5796675 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796681 : List Nat := [1, 2, 1, 1, 2, 5, 1, 1, 1, 1, 7]
def baseStart_5796681 : Nat := 118140960795 + 5796681 * 2 ^ 59
def prefixEnd_5796681 : Nat := 4983230072969 + 3 ^ 40 * 5796681 * 2
def baseEnd_5796681 : Nat := 2976483553785140192629055

theorem tailTrace_5796681 : CollatzResearch.WordTrace tailWord_5796681 prefixEnd_5796681 2976483553785140192629055 := by
  unfold tailWord_5796681
  simp only [CollatzResearch.WordTrace]
  refine ⟨211422325112622206142437897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140948216741748137428291931 211422325112622206142437897)
  ·
    refine ⟨158566743834466654606828423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211422325112622206142437897 158566743834466654606828423)
    ·
      refine ⟨237850115751699981910242635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158566743834466654606828423 237850115751699981910242635)
      ·
        refine ⟨356775173627549972865363953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237850115751699981910242635 356775173627549972865363953)
        ·
          refine ⟨267581380220662479649022965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 356775173627549972865363953 267581380220662479649022965)
          ·
            refine ⟨25085754395687107467095903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 267581380220662479649022965 25085754395687107467095903)
            ·
              refine ⟨37628631593530661200643855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25085754395687107467095903 37628631593530661200643855)
              ·
                refine ⟨56442947390295991800965783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37628631593530661200643855 56442947390295991800965783)
                ·
                  refine ⟨84664421085443987701448675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56442947390295991800965783 84664421085443987701448675)
                  ·
                    refine ⟨126996631628165981552173013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 84664421085443987701448675 126996631628165981552173013)
                    ·
                      refine ⟨2976483553785140192629055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 126996631628165981552173013 2976483553785140192629055)
                      ·
                        rfl

theorem cell23_5796681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 1, 7].length) (baseStart_5796681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796681 prefixEnd_5796681 := by exact prefixLift 5796681
  have htrace : WordTrace (prefixWord ++ tailWord_5796681) baseStart_5796681 baseEnd_5796681 := by
    simpa [prefixWord, tailWord_5796681, baseEnd_5796681] using wordTrace_append hprefix tailTrace_5796681
  have hstable : (prefixWord ++ tailWord_5796681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796681).length < 2 ^ (prefixWord ++ tailWord_5796681).sum := by decide
  have hdescent : baseEnd_5796681 < baseStart_5796681 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796691 : List Nat := [1, 1, 1, 2, 1, 1, 3, 3, 3, 3, 4]
def baseStart_5796691 : Nat := 118140960795 + 5796691 * 2 ^ 59
def prefixEnd_5796691 : Nat := 4983230072969 + 3 ^ 40 * 5796691 * 2
def baseEnd_5796691 : Nat := 2976488688591685153504009

theorem tailTrace_5796691 : CollatzResearch.WordTrace tailWord_5796691 prefixEnd_5796691 2976488688591685153504009 := by
  unfold tailWord_5796691
  simp only [CollatzResearch.WordTrace]
  refine ⟨211422689842585977850301927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140948459895057318566867951 211422689842585977850301927)
  ·
    refine ⟨317134034763878966775452891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211422689842585977850301927 317134034763878966775452891)
    ·
      refine ⟨475701052145818450163179337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317134034763878966775452891 475701052145818450163179337)
      ·
        refine ⟨356775789109363837622384503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 475701052145818450163179337 356775789109363837622384503)
        ·
          refine ⟨535163683664045756433576755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356775789109363837622384503 535163683664045756433576755)
          ·
            refine ⟨802745525496068634650365133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 535163683664045756433576755 802745525496068634650365133)
            ·
              refine ⟨301029572061025737993886925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 802745525496068634650365133 301029572061025737993886925)
              ·
                refine ⟨112886089522884651747707597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 301029572061025737993886925 112886089522884651747707597)
                ·
                  refine ⟨42332283571081744405390349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112886089522884651747707597 42332283571081744405390349)
                  ·
                    refine ⟨15874606339155654152021381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42332283571081744405390349 15874606339155654152021381)
                    ·
                      refine ⟨2976488688591685153504009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15874606339155654152021381 2976488688591685153504009)
                      ·
                        rfl

theorem cell23_5796691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 3, 4].length) (baseStart_5796691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796691 prefixEnd_5796691 := by exact prefixLift 5796691
  have htrace : WordTrace (prefixWord ++ tailWord_5796691) baseStart_5796691 baseEnd_5796691 := by
    simpa [prefixWord, tailWord_5796691, baseEnd_5796691] using wordTrace_append hprefix tailTrace_5796691
  have hstable : (prefixWord ++ tailWord_5796691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796691).length < 2 ^ (prefixWord ++ tailWord_5796691).sum := by decide
  have hdescent : baseEnd_5796691 < baseStart_5796691 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796725 : List Nat := [1, 3, 4, 1, 1, 2, 2, 2, 2, 1, 4]
def baseStart_5796725 : Nat := 118140960795 + 5796725 * 2 ^ 59
def prefixEnd_5796725 : Nat := 4983230072969 + 3 ^ 40 * 5796725 * 2
def baseEnd_5796725 : Nat := 2976506146933938020478853

theorem tailTrace_5796725 : CollatzResearch.WordTrace tailWord_5796725 prefixEnd_5796725 2976506146933938020478853 := by
  unfold tailWord_5796725
  simp only [CollatzResearch.WordTrace]
  refine ⟨211423929924462801657039629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140949286616308534438026419 211423929924462801657039629)
  ·
    refine ⟨79283973721673550621389861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211423929924462801657039629 79283973721673550621389861)
    ·
      refine ⟨14865745072813790741510599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79283973721673550621389861 14865745072813790741510599)
      ·
        refine ⟨22298617609220686112265899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14865745072813790741510599 22298617609220686112265899)
        ·
          refine ⟨33447926413831029168398849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22298617609220686112265899 33447926413831029168398849)
          ·
            refine ⟨25085944810373271876299137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33447926413831029168398849 25085944810373271876299137)
            ·
              refine ⟨18814458607779953907224353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25085944810373271876299137 18814458607779953907224353)
              ·
                refine ⟨14110843955834965430418265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18814458607779953907224353 14110843955834965430418265)
                ·
                  refine ⟨10583132966876224072813699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14110843955834965430418265 10583132966876224072813699)
                  ·
                    refine ⟨15874699450314336109220549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10583132966876224072813699 15874699450314336109220549)
                    ·
                      refine ⟨2976506146933938020478853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15874699450314336109220549 2976506146933938020478853)
                      ·
                        rfl

theorem cell23_5796725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_5796725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796725 prefixEnd_5796725 := by exact prefixLift 5796725
  have htrace : WordTrace (prefixWord ++ tailWord_5796725) baseStart_5796725 baseEnd_5796725 := by
    simpa [prefixWord, tailWord_5796725, baseEnd_5796725] using wordTrace_append hprefix tailTrace_5796725
  have hstable : (prefixWord ++ tailWord_5796725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796725).length < 2 ^ (prefixWord ++ tailWord_5796725).sum := by decide
  have hdescent : baseEnd_5796725 < baseStart_5796725 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796728 : List Nat := [2, 1, 2, 1, 1, 1, 1, 5, 4, 2, 3]
def baseStart_5796728 : Nat := 118140960795 + 5796728 * 2 ^ 59
def prefixEnd_5796728 : Nat := 4983230072969 + 3 ^ 40 * 5796728 * 2
def baseEnd_5796728 : Nat := 2976507687375901508741339

theorem tailTrace_5796728 : CollatzResearch.WordTrace tailWord_5796728 prefixEnd_5796728 2976507687375901508741339 := by
  unfold tailWord_5796728
  simp only [CollatzResearch.WordTrace]
  refine ⟨105712019671725966584699419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140949359562301288779599225 105712019671725966584699419)
  ·
    refine ⟨158568029507588949877049129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105712019671725966584699419 158568029507588949877049129)
    ·
      refine ⟨118926022130691712407786847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158568029507588949877049129 118926022130691712407786847)
      ·
        refine ⟨178389033196037568611680271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118926022130691712407786847 178389033196037568611680271)
        ·
          refine ⟨267583549794056352917520407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178389033196037568611680271 267583549794056352917520407)
          ·
            refine ⟨401375324691084529376280611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267583549794056352917520407 401375324691084529376280611)
            ·
              refine ⟨602062987036626794064420917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 401375324691084529376280611 602062987036626794064420917)
              ·
                refine ⟨56443405034683761943539461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 602062987036626794064420917 56443405034683761943539461)
                ·
                  refine ⟨10583138444003205364413649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56443405034683761943539461 10583138444003205364413649)
                  ·
                    refine ⟨7937353833002404023310237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10583138444003205364413649 7937353833002404023310237)
                    ·
                      refine ⟨2976507687375901508741339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7937353833002404023310237 2976507687375901508741339)
                      ·
                        rfl

theorem cell23_5796728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 4, 2, 3].length) (baseStart_5796728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796728 prefixEnd_5796728 := by exact prefixLift 5796728
  have htrace : WordTrace (prefixWord ++ tailWord_5796728) baseStart_5796728 baseEnd_5796728 := by
    simpa [prefixWord, tailWord_5796728, baseEnd_5796728] using wordTrace_append hprefix tailTrace_5796728
  have hstable : (prefixWord ++ tailWord_5796728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796728).length < 2 ^ (prefixWord ++ tailWord_5796728).sum := by decide
  have hdescent : baseEnd_5796728 < baseStart_5796728 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796731 : List Nat := [1, 1, 1, 1, 1, 5, 2, 3, 8]
def baseStart_5796731 : Nat := 118140960795 + 5796731 * 2 ^ 59
def prefixEnd_5796731 : Nat := 4983230072969 + 3 ^ 40 * 5796731 * 2
def baseEnd_5796731 : Nat := 330723247535318333000425

theorem tailTrace_5796731 : CollatzResearch.WordTrace tailWord_5796731 prefixEnd_5796731 330723247535318333000425 := by
  unfold tailWord_5796731
  simp only [CollatzResearch.WordTrace]
  refine ⟨211424148762441064681758047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140949432508294043121172031 211424148762441064681758047)
  ·
    refine ⟨317136223143661597022637071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211424148762441064681758047 317136223143661597022637071)
    ·
      refine ⟨475704334715492395533955607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317136223143661597022637071 475704334715492395533955607)
      ·
        refine ⟨713556502073238593300933411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475704334715492395533955607 713556502073238593300933411)
        ·
          refine ⟨1070334753109857889951400117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 713556502073238593300933411 1070334753109857889951400117)
          ·
            refine ⟨100343883104049177182943761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1070334753109857889951400117 100343883104049177182943761)
            ·
              refine ⟨75257912328036882887207821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100343883104049177182943761 75257912328036882887207821)
              ·
                refine ⟨28221717123013831082702933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75257912328036882887207821 28221717123013831082702933)
                ·
                  refine ⟨330723247535318333000425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28221717123013831082702933 330723247535318333000425)
                  ·
                    rfl

theorem cell23_5796731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 8].length) (baseStart_5796731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796731 prefixEnd_5796731 := by exact prefixLift 5796731
  have htrace : WordTrace (prefixWord ++ tailWord_5796731) baseStart_5796731 baseEnd_5796731 := by
    simpa [prefixWord, tailWord_5796731, baseEnd_5796731] using wordTrace_append hprefix tailTrace_5796731
  have hstable : (prefixWord ++ tailWord_5796731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796731).length < 2 ^ (prefixWord ++ tailWord_5796731).sum := by decide
  have hdescent : baseEnd_5796731 < baseStart_5796731 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796748 : List Nat := [2, 2, 1, 2, 1, 2, 4, 3, 6]
def baseStart_5796748 : Nat := 118140960795 + 5796748 * 2 ^ 59
def prefixEnd_5796748 : Nat := 4983230072969 + 3 ^ 40 * 5796748 * 2
def baseEnd_5796748 : Nat := 330724217443221270054583

theorem tailTrace_5796748 : CollatzResearch.WordTrace tailWord_5796748 prefixEnd_5796748 330724217443221270054583 := by
  unfold tailWord_5796748
  simp only [CollatzResearch.WordTrace]
  refine ⟨105712384401689738292563449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140949845868919651056751265 105712384401689738292563449)
  ·
    refine ⟨79284288301267303719422587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105712384401689738292563449 79284288301267303719422587)
    ·
      refine ⟨118926432451900955579133881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79284288301267303719422587 118926432451900955579133881)
      ·
        refine ⟨89194824338925716684350411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118926432451900955579133881 89194824338925716684350411)
        ·
          refine ⟨133792236508388575026525617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89194824338925716684350411 133792236508388575026525617)
          ·
            refine ⟨100344177381291431269894213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133792236508388575026525617 100344177381291431269894213)
            ·
              refine ⟨18814533258992143363105165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100344177381291431269894213 18814533258992143363105165)
              ·
                refine ⟨7055449972122053761164437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18814533258992143363105165 7055449972122053761164437)
                ·
                  refine ⟨330724217443221270054583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7055449972122053761164437 330724217443221270054583)
                  ·
                    rfl

theorem cell23_5796748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 3, 6].length) (baseStart_5796748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796748 prefixEnd_5796748 := by exact prefixLift 5796748
  have htrace : WordTrace (prefixWord ++ tailWord_5796748) baseStart_5796748 baseEnd_5796748 := by
    simpa [prefixWord, tailWord_5796748, baseEnd_5796748] using wordTrace_append hprefix tailTrace_5796748
  have hstable : (prefixWord ++ tailWord_5796748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796748).length < 2 ^ (prefixWord ++ tailWord_5796748).sum := by decide
  have hdescent : baseEnd_5796748 < baseStart_5796748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796769 : List Nat := [1, 2, 3, 4, 1, 2, 2, 3, 1, 4]
def baseStart_5796769 : Nat := 118140960795 + 5796769 * 2 ^ 59
def prefixEnd_5796769 : Nat := 4983230072969 + 3 ^ 40 * 5796769 * 2
def baseEnd_5796769 : Nat := 992176246694245282776217

theorem tailTrace_5796769 : CollatzResearch.WordTrace tailWord_5796769 prefixEnd_5796769 992176246694245282776217 := by
  unfold tailWord_5796769
  simp only [CollatzResearch.WordTrace]
  refine ⟨211425534736303397171641361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140950356490868931447760907 211425534736303397171641361)
  ·
    refine ⟨158569151052227547878731021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211425534736303397171641361 158569151052227547878731021)
    ·
      refine ⟨59463431644585330454524133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158569151052227547878731021 59463431644585330454524133)
      ·
        refine ⟨11149393433359749460223275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59463431644585330454524133 11149393433359749460223275)
        ·
          refine ⟨16724090150039624190334913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11149393433359749460223275 16724090150039624190334913)
          ·
            refine ⟨12543067612529718142751185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16724090150039624190334913 12543067612529718142751185)
            ·
              refine ⟨9407300709397288607063389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12543067612529718142751185 9407300709397288607063389)
              ·
                refine ⟨3527737766023983227648771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9407300709397288607063389 3527737766023983227648771)
                ·
                  refine ⟨5291606649035974841473157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3527737766023983227648771 5291606649035974841473157)
                  ·
                    refine ⟨992176246694245282776217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5291606649035974841473157 992176246694245282776217)
                    ·
                      rfl

theorem cell23_5796769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 3, 1, 4].length) (baseStart_5796769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796769 prefixEnd_5796769 := by exact prefixLift 5796769
  have htrace : WordTrace (prefixWord ++ tailWord_5796769) baseStart_5796769 baseEnd_5796769 := by
    simpa [prefixWord, tailWord_5796769, baseEnd_5796769] using wordTrace_append hprefix tailTrace_5796769
  have hstable : (prefixWord ++ tailWord_5796769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796769).length < 2 ^ (prefixWord ++ tailWord_5796769).sum := by decide
  have hdescent : baseEnd_5796769 < baseStart_5796769 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796792 : List Nat := [2, 1, 2, 1, 2, 5, 2, 1, 3, 1, 3]
def baseStart_5796792 : Nat := 118140960795 + 5796792 * 2 ^ 59
def prefixEnd_5796792 : Nat := 4983230072969 + 3 ^ 40 * 5796792 * 2
def baseEnd_5796792 : Nat := 2976540550137789258341045

theorem tailTrace_5796792 : CollatzResearch.WordTrace tailWord_5796792 prefixEnd_5796792 2976540550137789258341045 := by
  unfold tailWord_5796792
  simp only [CollatzResearch.WordTrace]
  refine ⟨105713186807610036049864315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140950915743480048066485753 105713186807610036049864315)
  ·
    refine ⟨158569780211415054074796473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105713186807610036049864315 158569780211415054074796473)
    ·
      refine ⟨118927335158561290556097355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158569780211415054074796473 118927335158561290556097355)
      ·
        refine ⟨178391002737841935834146033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118927335158561290556097355 178391002737841935834146033)
        ·
          refine ⟨133793252053381451875609525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178391002737841935834146033 133793252053381451875609525)
          ·
            refine ⟨12543117380004511113338393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 133793252053381451875609525 12543117380004511113338393)
            ·
              refine ⟨9407338035003383335003795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12543117380004511113338393 9407338035003383335003795)
              ·
                refine ⟨14111007052505075002505693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9407338035003383335003795 14111007052505075002505693)
                ·
                  refine ⟨5291627644689403125939635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14111007052505075002505693 5291627644689403125939635)
                  ·
                    refine ⟨7937441467034104688909453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5291627644689403125939635 7937441467034104688909453)
                    ·
                      refine ⟨2976540550137789258341045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7937441467034104688909453 2976540550137789258341045)
                      ·
                        rfl

theorem cell23_5796792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 3, 1, 3].length) (baseStart_5796792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796792 prefixEnd_5796792 := by exact prefixLift 5796792
  have htrace : WordTrace (prefixWord ++ tailWord_5796792) baseStart_5796792 baseEnd_5796792 := by
    simpa [prefixWord, tailWord_5796792, baseEnd_5796792] using wordTrace_append hprefix tailTrace_5796792
  have hstable : (prefixWord ++ tailWord_5796792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796792).length < 2 ^ (prefixWord ++ tailWord_5796792).sum := by decide
  have hdescent : baseEnd_5796792 < baseStart_5796792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796815 : List Nat := [1, 1, 2, 1, 1, 6, 1, 4, 1, 1, 4]
def baseStart_5796815 : Nat := 118140960795 + 5796815 * 2 ^ 59
def prefixEnd_5796815 : Nat := 4983230072969 + 3 ^ 40 * 5796815 * 2
def baseEnd_5796815 : Nat := 2976552360192842668353439

theorem tailTrace_5796815 : CollatzResearch.WordTrace tailWord_5796815 prefixEnd_5796815 2976552360192842668353439 := by
  unfold tailWord_5796815
  simp only [CollatzResearch.WordTrace]
  refine ⟨211427212494136747027815899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140951474996091164685210599 211427212494136747027815899)
  ·
    refine ⟨317140818741205120541723849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211427212494136747027815899 317140818741205120541723849)
    ·
      refine ⟨237855614055903840406292887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317140818741205120541723849 237855614055903840406292887)
      ·
        refine ⟨356783421083855760609439331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237855614055903840406292887 356783421083855760609439331)
        ·
          refine ⟨535175131625783640914158997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356783421083855760609439331 535175131625783640914158997)
          ·
            refine ⟨25086334294958608167851203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 535175131625783640914158997 25086334294958608167851203)
            ·
              refine ⟨37629501442437912251776805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25086334294958608167851203 37629501442437912251776805)
              ·
                refine ⟨7055531520457108547208151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37629501442437912251776805 7055531520457108547208151)
                ·
                  refine ⟨10583297280685662820812227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7055531520457108547208151 10583297280685662820812227)
                  ·
                    refine ⟨15874945921028494231218341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10583297280685662820812227 15874945921028494231218341)
                    ·
                      refine ⟨2976552360192842668353439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15874945921028494231218341 2976552360192842668353439)
                      ·
                        rfl

theorem cell23_5796815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 4, 1, 1, 4].length) (baseStart_5796815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796815 prefixEnd_5796815 := by exact prefixLift 5796815
  have htrace : WordTrace (prefixWord ++ tailWord_5796815) baseStart_5796815 baseEnd_5796815 := by
    simpa [prefixWord, tailWord_5796815, baseEnd_5796815] using wordTrace_append hprefix tailTrace_5796815
  have hstable : (prefixWord ++ tailWord_5796815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796815).length < 2 ^ (prefixWord ++ tailWord_5796815).sum := by decide
  have hdescent : baseEnd_5796815 < baseStart_5796815 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796825 : List Nat := [1, 2, 1, 2, 5, 1, 1, 2, 4, 4]
def baseStart_5796825 : Nat := 118140960795 + 5796825 * 2 ^ 59
def prefixEnd_5796825 : Nat := 4983230072969 + 3 ^ 40 * 5796825 * 2
def baseEnd_5796825 : Nat := 992185831666462543076131

theorem tailTrace_5796825 : CollatzResearch.WordTrace tailWord_5796825 prefixEnd_5796825 992185831666462543076131 := by
  unfold tailWord_5796825
  simp only [CollatzResearch.WordTrace]
  refine ⟨211427577224100518735679929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140951718149400345823786619 211427577224100518735679929)
  ·
    refine ⟨158570682918075389051759947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211427577224100518735679929 158570682918075389051759947)
    ·
      refine ⟨237856024377113083577639921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158570682918075389051759947 237856024377113083577639921)
      ·
        refine ⟨178392018282834812683229941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237856024377113083577639921 178392018282834812683229941)
        ·
          refine ⟨16724251714015763689052807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 178392018282834812683229941 16724251714015763689052807)
          ·
            refine ⟨25086377571023645533579211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16724251714015763689052807 25086377571023645533579211)
            ·
              refine ⟨37629566356535468300368817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25086377571023645533579211 37629566356535468300368817)
              ·
                refine ⟨28222174767401601225276613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37629566356535468300368817 28222174767401601225276613)
                ·
                  refine ⟨5291657768887800229739365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28222174767401601225276613 5291657768887800229739365)
                  ·
                    refine ⟨992185831666462543076131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5291657768887800229739365 992185831666462543076131)
                    ·
                      rfl

theorem cell23_5796825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 4, 4].length) (baseStart_5796825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796825 prefixEnd_5796825 := by exact prefixLift 5796825
  have htrace : WordTrace (prefixWord ++ tailWord_5796825) baseStart_5796825 baseEnd_5796825 := by
    simpa [prefixWord, tailWord_5796825, baseEnd_5796825] using wordTrace_append hprefix tailTrace_5796825
  have hstable : (prefixWord ++ tailWord_5796825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796825).length < 2 ^ (prefixWord ++ tailWord_5796825).sum := by decide
  have hdescent : baseEnd_5796825 < baseStart_5796825 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796826 : List Nat := [3, 1, 1, 2, 4, 3, 1, 3, 1, 1, 3]
def baseStart_5796826 : Nat := 118140960795 + 5796826 * 2 ^ 59
def prefixEnd_5796826 : Nat := 4983230072969 + 3 ^ 40 * 5796826 * 2
def baseEnd_5796826 : Nat := 2976558008480042125315889

theorem tailTrace_5796826 : CollatzResearch.WordTrace tailWord_5796826 prefixEnd_5796826 2976558008480042125315889 := by
  unfold tailWord_5796826
  simp only [CollatzResearch.WordTrace]
  refine ⟨52856903424274223976616583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140951742464731263937644221 52856903424274223976616583)
  ·
    refine ⟨79285355136411335964924875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52856903424274223976616583 79285355136411335964924875)
    ·
      refine ⟨118928032704617003947387313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79285355136411335964924875 118928032704617003947387313)
      ·
        refine ⟨89196024528462752960540485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118928032704617003947387313 89196024528462752960540485)
        ·
          refine ⟨16724254599086766180101341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89196024528462752960540485 16724254599086766180101341)
          ·
            refine ⟨6271595474657537317538003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16724254599086766180101341 6271595474657537317538003)
            ·
              refine ⟨9407393211986305976307005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6271595474657537317538003 9407393211986305976307005)
              ·
                refine ⟨3527772454494864741115127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9407393211986305976307005 3527772454494864741115127)
                ·
                  refine ⟨5291658681742297111672691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3527772454494864741115127 5291658681742297111672691)
                  ·
                    refine ⟨7937488022613445667509037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5291658681742297111672691 7937488022613445667509037)
                    ·
                      refine ⟨2976558008480042125315889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7937488022613445667509037 2976558008480042125315889)
                      ·
                        rfl

theorem cell23_5796826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 3, 1, 1, 3].length) (baseStart_5796826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796826 prefixEnd_5796826 := by exact prefixLift 5796826
  have htrace : WordTrace (prefixWord ++ tailWord_5796826) baseStart_5796826 baseEnd_5796826 := by
    simpa [prefixWord, tailWord_5796826, baseEnd_5796826] using wordTrace_append hprefix tailTrace_5796826
  have hstable : (prefixWord ++ tailWord_5796826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796826).length < 2 ^ (prefixWord ++ tailWord_5796826).sum := by decide
  have hdescent : baseEnd_5796826 < baseStart_5796826 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796835 : List Nat := [1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 5]
def baseStart_5796835 : Nat := 118140960795 + 5796835 * 2 ^ 59
def prefixEnd_5796835 : Nat := 4983230072969 + 3 ^ 40 * 5796835 * 2
def baseEnd_5796835 : Nat := 2976562629805932590103347

theorem tailTrace_5796835 : CollatzResearch.WordTrace tailWord_5796835 prefixEnd_5796835 2976562629805932590103347 := by
  unfold tailWord_5796835
  simp only [CollatzResearch.WordTrace]
  refine ⟨211427941954064290443543959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140951961302709526962362639 211427941954064290443543959)
  ·
    refine ⟨317141912931096435665315939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211427941954064290443543959 317141912931096435665315939)
    ·
      refine ⟨475712869396644653497973909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317141912931096435665315939 475712869396644653497973909)
      ·
        refine ⟨22299040752967718132717527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 475712869396644653497973909 22299040752967718132717527)
        ·
          refine ⟨33448561129451577199076291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22299040752967718132717527 33448561129451577199076291)
          ·
            refine ⟨50172841694177365798614437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33448561129451577199076291 50172841694177365798614437)
            ·
              refine ⟨9407407817658256087240207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50172841694177365798614437 9407407817658256087240207)
              ·
                refine ⟨14111111726487384130860311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9407407817658256087240207 14111111726487384130860311)
                ·
                  refine ⟨21166667589731076196290467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14111111726487384130860311 21166667589731076196290467)
                  ·
                    refine ⟨31750001384596614294435701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21166667589731076196290467 31750001384596614294435701)
                    ·
                      refine ⟨2976562629805932590103347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31750001384596614294435701 2976562629805932590103347)
                      ·
                        rfl

theorem cell23_5796835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_5796835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796835 prefixEnd_5796835 := by exact prefixLift 5796835
  have htrace : WordTrace (prefixWord ++ tailWord_5796835) baseStart_5796835 baseEnd_5796835 := by
    simpa [prefixWord, tailWord_5796835, baseEnd_5796835] using wordTrace_append hprefix tailTrace_5796835
  have hstable : (prefixWord ++ tailWord_5796835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796835).length < 2 ^ (prefixWord ++ tailWord_5796835).sum := by decide
  have hdescent : baseEnd_5796835 < baseStart_5796835 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796849 : List Nat := [1, 2, 2, 2, 4, 1, 3, 1, 3, 2, 2]
def baseStart_5796849 : Nat := 118140960795 + 5796849 * 2 ^ 59
def prefixEnd_5796849 : Nat := 4983230072969 + 3 ^ 40 * 5796849 * 2
def baseEnd_5796849 : Nat := 2976569818535095535328283

theorem tailTrace_5796849 : CollatzResearch.WordTrace tailWord_5796849 prefixEnd_5796849 2976569818535095535328283 := by
  unfold tailWord_5796849
  simp only [CollatzResearch.WordTrace]
  refine ⟨211428452576013570834553601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140952301717342380556369067 211428452576013570834553601)
  ·
    refine ⟨158571339432010178125915201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211428452576013570834553601 158571339432010178125915201)
    ·
      refine ⟨118928504574007633594436401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158571339432010178125915201 118928504574007633594436401)
      ·
        refine ⟨89196378430505725195827301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118928504574007633594436401 89196378430505725195827301)
        ·
          refine ⟨16724320955719823474217619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89196378430505725195827301 16724320955719823474217619)
          ·
            refine ⟨25086481433579735211326429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16724320955719823474217619 25086481433579735211326429)
            ·
              refine ⟨9407430537592400704247411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25086481433579735211326429 9407430537592400704247411)
              ·
                refine ⟨14111145806388601056371117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9407430537592400704247411 14111145806388601056371117)
                ·
                  refine ⟨5291679677395725396139169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14111145806388601056371117 5291679677395725396139169)
                  ·
                    refine ⟨3968759758046794047104377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5291679677395725396139169 3968759758046794047104377)
                    ·
                      refine ⟨2976569818535095535328283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3968759758046794047104377 2976569818535095535328283)
                      ·
                        rfl

theorem cell23_5796849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 3, 2, 2].length) (baseStart_5796849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796849 prefixEnd_5796849 := by exact prefixLift 5796849
  have htrace : WordTrace (prefixWord ++ tailWord_5796849) baseStart_5796849 baseEnd_5796849 := by
    simpa [prefixWord, tailWord_5796849, baseEnd_5796849] using wordTrace_append hprefix tailTrace_5796849
  have hstable : (prefixWord ++ tailWord_5796849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796849).length < 2 ^ (prefixWord ++ tailWord_5796849).sum := by decide
  have hdescent : baseEnd_5796849 < baseStart_5796849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796899 : List Nat := [1, 1, 1, 4, 3, 3, 2, 2, 2, 1, 3]
def baseStart_5796899 : Nat := 118140960795 + 5796899 * 2 ^ 59
def prefixEnd_5796899 : Nat := 4983230072969 + 3 ^ 40 * 5796899 * 2
def baseEnd_5796899 : Nat := 2976595492567820339703053

theorem tailTrace_5796899 : CollatzResearch.WordTrace tailWord_5796899 prefixEnd_5796899 2976595492567820339703053 := by
  unfold tailWord_5796899
  simp only [CollatzResearch.WordTrace]
  refine ⟨211430276225832429373873751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140953517483888286249249167 211430276225832429373873751)
  ·
    refine ⟨317145414338748644060810627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211430276225832429373873751 317145414338748644060810627)
    ·
      refine ⟨475718121508122966091215941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317145414338748644060810627 475718121508122966091215941)
      ·
        refine ⟨89197147782773056142102989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 475718121508122966091215941 89197147782773056142102989)
        ·
          refine ⟨33448930418539896053288621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89197147782773056142102989 33448930418539896053288621)
          ·
            refine ⟨12543348906952461019983233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33448930418539896053288621 12543348906952461019983233)
            ·
              refine ⟨9407511680214345764987425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12543348906952461019983233 9407511680214345764987425)
              ·
                refine ⟨7055633760160759323740569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9407511680214345764987425 7055633760160759323740569)
                ·
                  refine ⟨5291725320120569492805427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7055633760160759323740569 5291725320120569492805427)
                  ·
                    refine ⟨7937587980180854239208141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5291725320120569492805427 7937587980180854239208141)
                    ·
                      refine ⟨2976595492567820339703053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7937587980180854239208141 2976595492567820339703053)
                      ·
                        rfl

theorem cell23_5796899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 2, 2, 1, 3].length) (baseStart_5796899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796899 prefixEnd_5796899 := by exact prefixLift 5796899
  have htrace : WordTrace (prefixWord ++ tailWord_5796899) baseStart_5796899 baseEnd_5796899 := by
    simpa [prefixWord, tailWord_5796899, baseEnd_5796899] using wordTrace_append hprefix tailTrace_5796899
  have hstable : (prefixWord ++ tailWord_5796899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796899).length < 2 ^ (prefixWord ++ tailWord_5796899).sum := by decide
  have hdescent : baseEnd_5796899 < baseStart_5796899 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796900 : List Nat := [2, 3, 1, 4, 1, 3, 2, 2, 1, 2, 2]
def baseStart_5796900 : Nat := 118140960795 + 5796900 * 2 ^ 59
def prefixEnd_5796900 : Nat := 4983230072969 + 3 ^ 40 * 5796900 * 2
def baseEnd_5796900 : Nat := 2976596006048474835790549

theorem tailTrace_5796900 : CollatzResearch.WordTrace tailWord_5796900 prefixEnd_5796900 2976596006048474835790549 := by
  unfold tailWord_5796900
  simp only [CollatzResearch.WordTrace]
  refine ⟨105715156349414403272330077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140953541799219204363106769 105715156349414403272330077)
  ·
    refine ⟨39643183631030401227123779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105715156349414403272330077 39643183631030401227123779)
    ·
      refine ⟨59464775446545601840685669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39643183631030401227123779 59464775446545601840685669)
      ·
        refine ⟨11149645396227300345128563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59464775446545601840685669 11149645396227300345128563)
        ·
          refine ⟨16724468094340950517692845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11149645396227300345128563 16724468094340950517692845)
          ·
            refine ⟨6271675535377856444134817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16724468094340950517692845 6271675535377856444134817)
            ·
              refine ⟨4703756651533392333101113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6271675535377856444134817 4703756651533392333101113)
              ·
                refine ⟨3527817488650044249825835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4703756651533392333101113 3527817488650044249825835)
                ·
                  refine ⟨5291726232975066374738753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3527817488650044249825835 5291726232975066374738753)
                  ·
                    refine ⟨3968794674731299781054065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5291726232975066374738753 3968794674731299781054065)
                    ·
                      refine ⟨2976596006048474835790549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3968794674731299781054065 2976596006048474835790549)
                      ·
                        rfl

theorem cell23_5796900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_5796900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796900 prefixEnd_5796900 := by exact prefixLift 5796900
  have htrace : WordTrace (prefixWord ++ tailWord_5796900) baseStart_5796900 baseEnd_5796900 := by
    simpa [prefixWord, tailWord_5796900, baseEnd_5796900] using wordTrace_append hprefix tailTrace_5796900
  have hstable : (prefixWord ++ tailWord_5796900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796900).length < 2 ^ (prefixWord ++ tailWord_5796900).sum := by decide
  have hdescent : baseEnd_5796900 < baseStart_5796900 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796916 : List Nat := [2, 5, 1, 2, 1, 1, 2, 3, 2, 1, 3]
def baseStart_5796916 : Nat := 118140960795 + 5796916 * 2 ^ 59
def prefixEnd_5796916 : Nat := 4983230072969 + 3 ^ 40 * 5796916 * 2
def baseEnd_5796916 : Nat := 2976604221738946773190475

theorem tailTrace_5796916 : CollatzResearch.WordTrace tailWord_5796916 prefixEnd_5796916 2976604221738946773190475 := by
  unfold tailWord_5796916
  simp only [CollatzResearch.WordTrace]
  refine ⟨105715448133385420638621301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140953930844513894184828401 105715448133385420638621301)
  ·
    refine ⟨9910823262504883184870747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 105715448133385420638621301 9910823262504883184870747)
    ·
      refine ⟨14866234893757324777306121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9910823262504883184870747 14866234893757324777306121)
      ·
        refine ⟨11149676170317993582979591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14866234893757324777306121 11149676170317993582979591)
        ·
          refine ⟨16724514255476990374469387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11149676170317993582979591 16724514255476990374469387)
          ·
            refine ⟨25086771383215485561704081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16724514255476990374469387 25086771383215485561704081)
            ·
              refine ⟨18815078537411614171278061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25086771383215485561704081 18815078537411614171278061)
              ·
                refine ⟨7055654451529355314229273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18815078537411614171278061 7055654451529355314229273)
                ·
                  refine ⟨5291740838647016485671955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7055654451529355314229273 5291740838647016485671955)
                  ·
                    refine ⟨7937611257970524728507933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5291740838647016485671955 7937611257970524728507933)
                    ·
                      refine ⟨2976604221738946773190475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7937611257970524728507933 2976604221738946773190475)
                      ·
                        rfl

theorem cell23_5796916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_5796916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796916 prefixEnd_5796916 := by exact prefixLift 5796916
  have htrace : WordTrace (prefixWord ++ tailWord_5796916) baseStart_5796916 baseEnd_5796916 := by
    simpa [prefixWord, tailWord_5796916, baseEnd_5796916] using wordTrace_append hprefix tailTrace_5796916
  have hstable : (prefixWord ++ tailWord_5796916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796916).length < 2 ^ (prefixWord ++ tailWord_5796916).sum := by decide
  have hdescent : baseEnd_5796916 < baseStart_5796916 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796922 : List Nat := [3, 1, 1, 1, 3, 1, 3, 3, 1, 4, 2]
def baseStart_5796922 : Nat := 118140960795 + 5796922 * 2 ^ 59
def prefixEnd_5796922 : Nat := 4983230072969 + 3 ^ 40 * 5796922 * 2
def baseEnd_5796922 : Nat := 2976607302622873749715447

theorem tailTrace_5796922 : CollatzResearch.WordTrace tailWord_5796922 prefixEnd_5796922 2976607302622873749715447 := by
  unfold tailWord_5796922
  simp only [CollatzResearch.WordTrace]
  refine ⟨52857778776187276075490255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140954076736499402867974013 52857778776187276075490255)
  ·
    refine ⟨79286668164280914113235383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52857778776187276075490255 79286668164280914113235383)
    ·
      refine ⟨118930002246421371169853075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79286668164280914113235383 118930002246421371169853075)
      ·
        refine ⟨178395003369632056754779613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118930002246421371169853075 178395003369632056754779613)
        ·
          refine ⟨66898126263612021283042355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178395003369632056754779613 66898126263612021283042355)
          ·
            refine ⟨100347189395418031924563533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66898126263612021283042355 100347189395418031924563533)
            ·
              refine ⟨37630196023281761971711325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100347189395418031924563533 37630196023281761971711325)
              ·
                refine ⟨14111323508730660739391747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37630196023281761971711325 14111323508730660739391747)
                ·
                  refine ⟨21166985263095991109087621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14111323508730660739391747 21166985263095991109087621)
                  ·
                    refine ⟨3968809736830498332953929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21166985263095991109087621 3968809736830498332953929)
                    ·
                      refine ⟨2976607302622873749715447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3968809736830498332953929 2976607302622873749715447)
                      ·
                        rfl

theorem cell23_5796922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 1, 4, 2].length) (baseStart_5796922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796922 prefixEnd_5796922 := by exact prefixLift 5796922
  have htrace : WordTrace (prefixWord ++ tailWord_5796922) baseStart_5796922 baseEnd_5796922 := by
    simpa [prefixWord, tailWord_5796922, baseEnd_5796922] using wordTrace_append hprefix tailTrace_5796922
  have hstable : (prefixWord ++ tailWord_5796922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796922).length < 2 ^ (prefixWord ++ tailWord_5796922).sum := by decide
  have hdescent : baseEnd_5796922 < baseStart_5796922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796950 : List Nat := [5, 2, 2, 1, 2, 2, 1, 2, 2, 1, 3]
def baseStart_5796950 : Nat := 118140960795 + 5796950 * 2 ^ 59
def prefixEnd_5796950 : Nat := 4983230072969 + 3 ^ 40 * 5796950 * 2
def baseEnd_5796950 : Nat := 2976621680081199640165319

theorem tailTrace_5796950 : CollatzResearch.WordTrace tailWord_5796950 prefixEnd_5796950 2976621680081199640165319 := by
  unfold tailWord_5796950
  simp only [CollatzResearch.WordTrace]
  refine ⟨13214508521790479067748769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 140954757565765110055986869 13214508521790479067748769)
  ·
    refine ⟨9910881391342859300811577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13214508521790479067748769 9910881391342859300811577)
    ·
      refine ⟨7433161043507144475608683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9910881391342859300811577 7433161043507144475608683)
      ·
        refine ⟨11149741565260716713413025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7433161043507144475608683 11149741565260716713413025)
        ·
          refine ⟨8362306173945537535059769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11149741565260716713413025 8362306173945537535059769)
          ·
            refine ⟨6271729630459153151294827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8362306173945537535059769 6271729630459153151294827)
            ·
              refine ⟨9407594445688729726942241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6271729630459153151294827 9407594445688729726942241)
              ·
                refine ⟨7055695834266547295206681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9407594445688729726942241 7055695834266547295206681)
                ·
                  refine ⟨5291771875699910471405011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7055695834266547295206681 5291771875699910471405011)
                  ·
                    refine ⟨7937657813549865707107517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5291771875699910471405011 7937657813549865707107517)
                    ·
                      refine ⟨2976621680081199640165319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7937657813549865707107517 2976621680081199640165319)
                      ·
                        rfl

theorem cell23_5796950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_5796950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796950 prefixEnd_5796950 := by exact prefixLift 5796950
  have htrace : WordTrace (prefixWord ++ tailWord_5796950) baseStart_5796950 baseEnd_5796950 := by
    simpa [prefixWord, tailWord_5796950, baseEnd_5796950] using wordTrace_append hprefix tailTrace_5796950
  have hstable : (prefixWord ++ tailWord_5796950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796950).length < 2 ^ (prefixWord ++ tailWord_5796950).sum := by decide
  have hdescent : baseEnd_5796950 < baseStart_5796950 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796962 : List Nat := [3, 3, 2, 2, 1, 1, 1, 3, 7]
def baseStart_5796962 : Nat := 118140960795 + 5796962 * 2 ^ 59
def prefixEnd_5796962 : Nat := 4983230072969 + 3 ^ 40 * 5796962 * 2
def baseEnd_5796962 : Nat := 330736426872117065912807

theorem tailTrace_5796962 : CollatzResearch.WordTrace tailWord_5796962 prefixEnd_5796962 330736426872117065912807 := by
  unfold tailWord_5796962
  simp only [CollatzResearch.WordTrace]
  refine ⟨52858143506151047783354285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140955049349736127422278093 52858143506151047783354285)
  ·
    refine ⟨19821803814806642918757857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52858143506151047783354285 19821803814806642918757857)
    ·
      refine ⟨14866352861104982189068393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19821803814806642918757857 14866352861104982189068393)
      ·
        refine ⟨11149764645828736641801295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14866352861104982189068393 11149764645828736641801295)
        ·
          refine ⟨16724646968743104962701943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11149764645828736641801295 16724646968743104962701943)
          ·
            refine ⟨25086970453114657444052915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16724646968743104962701943 25086970453114657444052915)
            ·
              refine ⟨37630455679671986166079373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25086970453114657444052915 37630455679671986166079373)
              ·
                refine ⟨14111420879876994812279765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37630455679671986166079373 14111420879876994812279765)
                ·
                  refine ⟨330736426872117065912807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14111420879876994812279765 330736426872117065912807)
                  ·
                    rfl

theorem cell23_5796962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 7].length) (baseStart_5796962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796962 prefixEnd_5796962 := by exact prefixLift 5796962
  have htrace : WordTrace (prefixWord ++ tailWord_5796962) baseStart_5796962 baseEnd_5796962 := by
    simpa [prefixWord, tailWord_5796962, baseEnd_5796962] using wordTrace_append hprefix tailTrace_5796962
  have hstable : (prefixWord ++ tailWord_5796962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796962).length < 2 ^ (prefixWord ++ tailWord_5796962).sum := by decide
  have hdescent : baseEnd_5796962 < baseStart_5796962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796973 : List Nat := [1, 5, 1, 1, 2, 3, 3, 1, 2, 2, 2]
def baseStart_5796973 : Nat := 118140960795 + 5796973 * 2 ^ 59
def prefixEnd_5796973 : Nat := 4983230072969 + 3 ^ 40 * 5796973 * 2
def baseEnd_5796973 : Nat := 2976633490136253050177713

theorem tailTrace_5796973 : CollatzResearch.WordTrace tailWord_5796973 prefixEnd_5796973 2976633490136253050177713 := by
  unfold tailWord_5796973
  simp only [CollatzResearch.WordTrace]
  refine ⟨211432975227564340012067573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140955316818376226674711715 211432975227564340012067573)
  ·
    refine ⟨19821841427584156876131335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 211432975227564340012067573 19821841427584156876131335)
    ·
      refine ⟨29732762141376235314197003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19821841427584156876131335 29732762141376235314197003)
      ·
        refine ⟨44599143212064352971295505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29732762141376235314197003 44599143212064352971295505)
        ·
          refine ⟨33449357409048264728471629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44599143212064352971295505 33449357409048264728471629)
          ·
            refine ⟨12543509028393099273176861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33449357409048264728471629 12543509028393099273176861)
            ·
              refine ⟨4703815885647412227441323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12543509028393099273176861 4703815885647412227441323)
              ·
                refine ⟨7055723828471118341161985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4703815885647412227441323 7055723828471118341161985)
                ·
                  refine ⟨5291792871353338755871489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7055723828471118341161985 5291792871353338755871489)
                  ·
                    refine ⟨3968844653515004066903617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5291792871353338755871489 3968844653515004066903617)
                    ·
                      refine ⟨2976633490136253050177713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3968844653515004066903617 2976633490136253050177713)
                      ·
                        rfl

theorem cell23_5796973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 1, 2, 2, 2].length) (baseStart_5796973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796973 prefixEnd_5796973 := by exact prefixLift 5796973
  have htrace : WordTrace (prefixWord ++ tailWord_5796973) baseStart_5796973 baseEnd_5796973 := by
    simpa [prefixWord, tailWord_5796973, baseEnd_5796973] using wordTrace_append hprefix tailTrace_5796973
  have hstable : (prefixWord ++ tailWord_5796973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796973).length < 2 ^ (prefixWord ++ tailWord_5796973).sum := by decide
  have hdescent : baseEnd_5796973 < baseStart_5796973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5796995 : List Nat := [1, 1, 1, 3, 3, 2, 1, 3, 1, 3, 4]
def baseStart_5796995 : Nat := 118140960795 + 5796995 * 2 ^ 59
def prefixEnd_5796995 : Nat := 4983230072969 + 3 ^ 40 * 5796995 * 2
def baseEnd_5796995 : Nat := 2976644786710651964102611

theorem tailTrace_5796995 : CollatzResearch.WordTrace tailWord_5796995 prefixEnd_5796995 2976644786710651964102611 := by
  unfold tailWord_5796995
  simp only [CollatzResearch.WordTrace]
  refine ⟨211433777633484637769368439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140955851755656425179578959 211433777633484637769368439)
  ·
    refine ⟨317150666450226956654052659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211433777633484637769368439 317150666450226956654052659)
    ·
      refine ⟨475725999675340434981078989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317150666450226956654052659 475725999675340434981078989)
      ·
        refine ⟨178397249878252663117904621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 475725999675340434981078989 178397249878252663117904621)
        ·
          refine ⟨66898968704344748669214233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178397249878252663117904621 66898968704344748669214233)
          ·
            refine ⟨50174226528258561501910675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66898968704344748669214233 50174226528258561501910675)
            ·
              refine ⟨75261339792387842252866013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50174226528258561501910675 75261339792387842252866013)
              ·
                refine ⟨28223002422145440844824755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75261339792387842252866013 28223002422145440844824755)
                ·
                  refine ⟨42334503633218161267237133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28223002422145440844824755 42334503633218161267237133)
                  ·
                    refine ⟨15875438862456810475213925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42334503633218161267237133 15875438862456810475213925)
                    ·
                      refine ⟨2976644786710651964102611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15875438862456810475213925 2976644786710651964102611)
                      ·
                        rfl

theorem cell23_5796995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 3, 4].length) (baseStart_5796995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5796995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5796995 prefixEnd_5796995 := by exact prefixLift 5796995
  have htrace : WordTrace (prefixWord ++ tailWord_5796995) baseStart_5796995 baseEnd_5796995 := by
    simpa [prefixWord, tailWord_5796995, baseEnd_5796995] using wordTrace_append hprefix tailTrace_5796995
  have hstable : (prefixWord ++ tailWord_5796995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5796995).length < 2 ^ (prefixWord ++ tailWord_5796995).sum := by decide
  have hdescent : baseEnd_5796995 < baseStart_5796995 := by decide
  rcases family_descends (prefixWord ++ tailWord_5796995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797049 : List Nat := [1, 2, 1, 4, 1, 4, 2, 1, 2, 2, 3]
def baseStart_5797049 : Nat := 118140960795 + 5797049 * 2 ^ 59
def prefixEnd_5797049 : Nat := 4983230072969 + 3 ^ 40 * 5797049 * 2
def baseEnd_5797049 : Nat := 2976672514665994752827363

theorem tailTrace_5797049 : CollatzResearch.WordTrace tailWord_5797049 prefixEnd_5797049 2976672514665994752827363 := by
  unfold tailWord_5797049
  simp only [CollatzResearch.WordTrace]
  refine ⟨211435747175289004991834201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140957164783526003327889467 211435747175289004991834201)
  ·
    refine ⟨158576810381466753743875651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211435747175289004991834201 158576810381466753743875651)
    ·
      refine ⟨237865215572200130615813477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158576810381466753743875651 237865215572200130615813477)
      ·
        refine ⟨44599727919787524490465027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 237865215572200130615813477 44599727919787524490465027)
        ·
          refine ⟨66899591879681286735697541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44599727919787524490465027 66899591879681286735697541)
          ·
            refine ⟨12543673477440241262943289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66899591879681286735697541 12543673477440241262943289)
            ·
              refine ⟨9407755108080180947207467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12543673477440241262943289 9407755108080180947207467)
              ·
                refine ⟨14111632662120271420811201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9407755108080180947207467 14111632662120271420811201)
                ·
                  refine ⟨10583724496590203565608401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14111632662120271420811201 10583724496590203565608401)
                  ·
                    refine ⟨7937793372442652674206301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10583724496590203565608401 7937793372442652674206301)
                    ·
                      refine ⟨2976672514665994752827363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7937793372442652674206301 2976672514665994752827363)
                      ·
                        rfl

theorem cell23_5797049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_5797049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797049 prefixEnd_5797049 := by exact prefixLift 5797049
  have htrace : WordTrace (prefixWord ++ tailWord_5797049) baseStart_5797049 baseEnd_5797049 := by
    simpa [prefixWord, tailWord_5797049, baseEnd_5797049] using wordTrace_append hprefix tailTrace_5797049
  have hstable : (prefixWord ++ tailWord_5797049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797049).length < 2 ^ (prefixWord ++ tailWord_5797049).sum := by decide
  have hdescent : baseEnd_5797049 < baseStart_5797049 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797106 : List Nat := [3, 2, 1, 3, 3, 1, 1, 1, 1, 5, 2]
def baseStart_5797106 : Nat := 118140960795 + 5797106 * 2 ^ 59
def prefixEnd_5797106 : Nat := 4983230072969 + 3 ^ 40 * 5797106 * 2
def baseEnd_5797106 : Nat := 2976701783063301029814601

theorem tailTrace_5797106 : CollatzResearch.WordTrace tailWord_5797106 prefixEnd_5797106 2976701783063301029814601 := by
  unfold tailWord_5797106
  simp only [CollatzResearch.WordTrace]
  refine ⟨52859456534020625931664793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140958550757388335817772781 52859456534020625931664793)
  ·
    refine ⟨39644592400515469448748595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52859456534020625931664793 39644592400515469448748595)
    ·
      refine ⟨59466888600773204173122893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39644592400515469448748595 59466888600773204173122893)
      ·
        refine ⟨22300083225289951564921085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59466888600773204173122893 22300083225289951564921085)
        ·
          refine ⟨8362531209483731836845407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22300083225289951564921085 8362531209483731836845407)
          ·
            refine ⟨12543796814225597755268111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8362531209483731836845407 12543796814225597755268111)
            ·
              refine ⟨18815695221338396632902167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12543796814225597755268111 18815695221338396632902167)
              ·
                refine ⟨28223542832007594949353251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18815695221338396632902167 28223542832007594949353251)
                ·
                  refine ⟨42335314248011392424029877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28223542832007594949353251 42335314248011392424029877)
                  ·
                    refine ⟨3968935710751068039752801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42335314248011392424029877 3968935710751068039752801)
                    ·
                      refine ⟨2976701783063301029814601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3968935710751068039752801 2976701783063301029814601)
                      ·
                        rfl

theorem cell23_5797106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_5797106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797106 prefixEnd_5797106 := by exact prefixLift 5797106
  have htrace : WordTrace (prefixWord ++ tailWord_5797106) baseStart_5797106 baseEnd_5797106 := by
    simpa [prefixWord, tailWord_5797106, baseEnd_5797106] using wordTrace_append hprefix tailTrace_5797106
  have hstable : (prefixWord ++ tailWord_5797106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797106).length < 2 ^ (prefixWord ++ tailWord_5797106).sum := by decide
  have hdescent : baseEnd_5797106 < baseStart_5797106 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797119 : List Nat := [1, 1, 2, 2, 1, 6, 1, 3, 1, 1, 4]
def baseStart_5797119 : Nat := 118140960795 + 5797119 * 2 ^ 59
def prefixEnd_5797119 : Nat := 4983230072969 + 3 ^ 40 * 5797119 * 2
def baseEnd_5797119 : Nat := 2976708458311809478952041

theorem tailTrace_5797119 : CollatzResearch.WordTrace tailWord_5797119 prefixEnd_5797119 2976708458311809478952041 := by
  unfold tailWord_5797119
  simp only [CollatzResearch.WordTrace]
  refine ⟨211438300285035406946882411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140958866856690271297921607 211438300285035406946882411)
  ·
    refine ⟨317157450427553110420323617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211438300285035406946882411 317157450427553110420323617)
    ·
      refine ⟨237868087820664832815242713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317157450427553110420323617 237868087820664832815242713)
      ·
        refine ⟨178401065865498624611432035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237868087820664832815242713 178401065865498624611432035)
        ·
          refine ⟨267601598798247936917148053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178401065865498624611432035 267601598798247936917148053)
          ·
            refine ⟨12543824943667872042991315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 267601598798247936917148053 12543824943667872042991315)
            ·
              refine ⟨18815737415501808064486973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12543824943667872042991315 18815737415501808064486973)
              ·
                refine ⟨7055901530813178024182615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18815737415501808064486973 7055901530813178024182615)
                ·
                  refine ⟨10583852296219767036273923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7055901530813178024182615 10583852296219767036273923)
                  ·
                    refine ⟨15875778444329650554410885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10583852296219767036273923 15875778444329650554410885)
                    ·
                      refine ⟨2976708458311809478952041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15875778444329650554410885 2976708458311809478952041)
                      ·
                        rfl

theorem cell23_5797119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 3, 1, 1, 4].length) (baseStart_5797119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797119 prefixEnd_5797119 := by exact prefixLift 5797119
  have htrace : WordTrace (prefixWord ++ tailWord_5797119) baseStart_5797119 baseEnd_5797119 := by
    simpa [prefixWord, tailWord_5797119, baseEnd_5797119] using wordTrace_append hprefix tailTrace_5797119
  have hstable : (prefixWord ++ tailWord_5797119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797119).length < 2 ^ (prefixWord ++ tailWord_5797119).sum := by decide
  have hdescent : baseEnd_5797119 < baseStart_5797119 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797125 : List Nat := [1, 3, 1, 1, 2, 1, 14]
def baseStart_5797125 : Nat := 118140960795 + 5797125 * 2 ^ 59
def prefixEnd_5797125 : Nat := 4983230072969 + 3 ^ 40 * 5797125 * 2
def baseEnd_5797125 : Nat := 36749525175256005623173

theorem tailTrace_5797125 : CollatzResearch.WordTrace tailWord_5797125 prefixEnd_5797125 36749525175256005623173 := by
  unfold tailWord_5797125
  simp only [CollatzResearch.WordTrace]
  refine ⟨211438519123013669971600829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140959012748675779981067219 211438519123013669971600829)
  ·
    refine ⟨79289444671130126239350311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211438519123013669971600829 79289444671130126239350311)
    ·
      refine ⟨118934167006695189359025467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79289444671130126239350311 118934167006695189359025467)
      ·
        refine ⟨178401250510042784038538201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118934167006695189359025467 178401250510042784038538201)
        ·
          refine ⟨133800937882532088028903651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178401250510042784038538201 133800937882532088028903651)
          ·
            refine ⟨200701406823798132043355477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133800937882532088028903651 200701406823798132043355477)
            ·
              refine ⟨36749525175256005623173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 200701406823798132043355477 36749525175256005623173)
              ·
                rfl

theorem cell23_5797125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 14].length) (baseStart_5797125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797125 prefixEnd_5797125 := by exact prefixLift 5797125
  have htrace : WordTrace (prefixWord ++ tailWord_5797125) baseStart_5797125 baseEnd_5797125 := by
    simpa [prefixWord, tailWord_5797125, baseEnd_5797125] using wordTrace_append hprefix tailTrace_5797125
  have hstable : (prefixWord ++ tailWord_5797125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797125).length < 2 ^ (prefixWord ++ tailWord_5797125).sum := by decide
  have hdescent : baseEnd_5797125 < baseStart_5797125 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797135 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 7]
def baseStart_5797135 : Nat := 118140960795 + 5797135 * 2 ^ 59
def prefixEnd_5797135 : Nat := 4983230072969 + 3 ^ 40 * 5797135 * 2
def baseEnd_5797135 : Nat := 2976716674002281416351967

theorem tailTrace_5797135 : CollatzResearch.WordTrace tailWord_5797135 prefixEnd_5797135 2976716674002281416351967 := by
  unfold tailWord_5797135
  simp only [CollatzResearch.WordTrace]
  refine ⟨211438883852977441679464859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140959255901984961119643239 211438883852977441679464859)
  ·
    refine ⟨317158325779466162519197289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211438883852977441679464859 317158325779466162519197289)
    ·
      refine ⟨237868744334599621889397967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317158325779466162519197289 237868744334599621889397967)
      ·
        refine ⟨356803116501899432834096951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237868744334599621889397967 356803116501899432834096951)
        ·
          refine ⟨535204674752849149251145427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356803116501899432834096951 535204674752849149251145427)
          ·
            refine ⟨802807012129273723876718141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 535204674752849149251145427 802807012129273723876718141)
            ·
              refine ⟨301052629548477646453769303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 802807012129273723876718141 301052629548477646453769303)
              ·
                refine ⟨451578944322716469680653955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 301052629548477646453769303 451578944322716469680653955)
                ·
                  refine ⟨677368416484074704520980933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 451578944322716469680653955 677368416484074704520980933)
                  ·
                    refine ⟨127006578090764007097683925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 677368416484074704520980933 127006578090764007097683925)
                    ·
                      refine ⟨2976716674002281416351967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 127006578090764007097683925 2976716674002281416351967)
                      ·
                        rfl

theorem cell23_5797135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 7].length) (baseStart_5797135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797135 prefixEnd_5797135 := by exact prefixLift 5797135
  have htrace : WordTrace (prefixWord ++ tailWord_5797135) baseStart_5797135 baseEnd_5797135 := by
    simpa [prefixWord, tailWord_5797135, baseEnd_5797135] using wordTrace_append hprefix tailTrace_5797135
  have hstable : (prefixWord ++ tailWord_5797135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797135).length < 2 ^ (prefixWord ++ tailWord_5797135).sum := by decide
  have hdescent : baseEnd_5797135 < baseStart_5797135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797149 : List Nat := [1, 4, 2, 3, 1, 2, 1, 1, 1, 1, 6]
def baseStart_5797149 : Nat := 118140960795 + 5797149 * 2 ^ 59
def prefixEnd_5797149 : Nat := 4983230072969 + 3 ^ 40 * 5797149 * 2
def baseEnd_5797149 : Nat := 2976723862731444361576903

theorem tailTrace_5797149 : CollatzResearch.WordTrace tailWord_5797149 prefixEnd_5797149 2976723862731444361576903 := by
  unfold tailWord_5797149
  simp only [CollatzResearch.WordTrace]
  refine ⟨211439394474926722070474501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140959596316617814713649667 211439394474926722070474501)
  ·
    refine ⟨39644886464048760388213969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 211439394474926722070474501 39644886464048760388213969)
    ·
      refine ⟨29733664848036570291160477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39644886464048760388213969 29733664848036570291160477)
      ·
        refine ⟨11150124318013713859185179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29733664848036570291160477 11150124318013713859185179)
        ·
          refine ⟨16725186477020570788777769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11150124318013713859185179 16725186477020570788777769)
          ·
            refine ⟨12543889857765428091583327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16725186477020570788777769 12543889857765428091583327)
            ·
              refine ⟨18815834786648142137374991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12543889857765428091583327 18815834786648142137374991)
              ·
                refine ⟨28223752179972213206062487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18815834786648142137374991 28223752179972213206062487)
                ·
                  refine ⟨42335628269958319809093731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28223752179972213206062487 42335628269958319809093731)
                  ·
                    refine ⟨63503442404937479713640597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42335628269958319809093731 63503442404937479713640597)
                    ·
                      refine ⟨2976723862731444361576903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63503442404937479713640597 2976723862731444361576903)
                      ·
                        rfl

theorem cell23_5797149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_5797149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797149 prefixEnd_5797149 := by exact prefixLift 5797149
  have htrace : WordTrace (prefixWord ++ tailWord_5797149) baseStart_5797149 baseEnd_5797149 := by
    simpa [prefixWord, tailWord_5797149, baseEnd_5797149] using wordTrace_append hprefix tailTrace_5797149
  have hstable : (prefixWord ++ tailWord_5797149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797149).length < 2 ^ (prefixWord ++ tailWord_5797149).sum := by decide
  have hdescent : baseEnd_5797149 < baseStart_5797149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797156 : List Nat := [2, 3, 1, 3, 1, 1, 4, 2, 1, 2, 3]
def baseStart_5797156 : Nat := 118140960795 + 5797156 * 2 ^ 59
def prefixEnd_5797156 : Nat := 4983230072969 + 3 ^ 40 * 5797156 * 2
def baseEnd_5797156 : Nat := 2976727457096025834189371

theorem tailTrace_5797156 : CollatzResearch.WordTrace tailWord_5797156 prefixEnd_5797156 2976727457096025834189371 := by
  unfold tailWord_5797156
  simp only [CollatzResearch.WordTrace]
  refine ⟨105719824892950681132989661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140959766523934241510652881 105719824892950681132989661)
  ·
    refine ⟨39644934334856505424871123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105719824892950681132989661 39644934334856505424871123)
    ·
      refine ⟨59467401502284758137306685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39644934334856505424871123 59467401502284758137306685)
      ·
        refine ⟨22300275563356784301490007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59467401502284758137306685 22300275563356784301490007)
        ·
          refine ⟨33450413345035176452235011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22300275563356784301490007 33450413345035176452235011)
          ·
            refine ⟨50175620017552764678352517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33450413345035176452235011 50175620017552764678352517)
            ·
              refine ⟨9407928753291143377191097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50175620017552764678352517 9407928753291143377191097)
              ·
                refine ⟨7055946564968357532893323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9407928753291143377191097 7055946564968357532893323)
                ·
                  refine ⟨10583919847452536299339985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7055946564968357532893323 10583919847452536299339985)
                  ·
                    refine ⟨7937939885589402224504989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10583919847452536299339985 7937939885589402224504989)
                    ·
                      refine ⟨2976727457096025834189371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7937939885589402224504989 2976727457096025834189371)
                      ·
                        rfl

theorem cell23_5797156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_5797156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797156 prefixEnd_5797156 := by exact prefixLift 5797156
  have htrace : WordTrace (prefixWord ++ tailWord_5797156) baseStart_5797156 baseEnd_5797156 := by
    simpa [prefixWord, tailWord_5797156, baseEnd_5797156] using wordTrace_append hprefix tailTrace_5797156
  have hstable : (prefixWord ++ tailWord_5797156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797156).length < 2 ^ (prefixWord ++ tailWord_5797156).sum := by decide
  have hdescent : baseEnd_5797156 < baseStart_5797156 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797170 : List Nat := [3, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2]
def baseStart_5797170 : Nat := 118140960795 + 5797170 * 2 ^ 59
def prefixEnd_5797170 : Nat := 4983230072969 + 3 ^ 40 * 5797170 * 2
def baseEnd_5797170 : Nat := 2976734645825188779414307

theorem tailTrace_5797170 : CollatzResearch.WordTrace tailWord_5797170 prefixEnd_5797170 2976734645825188779414307 := by
  unfold tailWord_5797170
  simp only [CollatzResearch.WordTrace]
  refine ⟨52860040101962660664247241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140960106938567095104659309 52860040101962660664247241)
  ·
    refine ⟨39645030076471995498185431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52860040101962660664247241 39645030076471995498185431)
    ·
      refine ⟨59467545114707993247278147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39645030076471995498185431 59467545114707993247278147)
      ·
        refine ⟨89201317672061989870917221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59467545114707993247278147 89201317672061989870917221)
        ·
          refine ⟨16725247063511623100796979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89201317672061989870917221 16725247063511623100796979)
          ·
            refine ⟨25087870595267434651195469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16725247063511623100796979 25087870595267434651195469)
            ·
              refine ⟨9407951473225287994198301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25087870595267434651195469 9407951473225287994198301)
              ·
                refine ⟨3527981802459482997824363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9407951473225287994198301 3527981802459482997824363)
                ·
                  refine ⟨5291972703689224496736545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3527981802459482997824363 5291972703689224496736545)
                  ·
                    refine ⟨3968979527766918372552409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5291972703689224496736545 3968979527766918372552409)
                    ·
                      refine ⟨2976734645825188779414307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3968979527766918372552409 2976734645825188779414307)
                      ·
                        rfl

theorem cell23_5797170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2].length) (baseStart_5797170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797170 prefixEnd_5797170 := by exact prefixLift 5797170
  have htrace : WordTrace (prefixWord ++ tailWord_5797170) baseStart_5797170 baseEnd_5797170 := by
    simpa [prefixWord, tailWord_5797170, baseEnd_5797170] using wordTrace_append hprefix tailTrace_5797170
  have hstable : (prefixWord ++ tailWord_5797170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797170).length < 2 ^ (prefixWord ++ tailWord_5797170).sum := by decide
  have hdescent : baseEnd_5797170 < baseStart_5797170 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797192 : List Nat := [2, 1, 3, 1, 1, 2, 1, 3, 2, 3, 4]
def baseStart_5797192 : Nat := 118140960795 + 5797192 * 2 ^ 59
def prefixEnd_5797192 : Nat := 4983230072969 + 3 ^ 40 * 5797192 * 2
def baseEnd_5797192 : Nat := 2976745942399587693339205

theorem tailTrace_5797192 : CollatzResearch.WordTrace tailWord_5797192 prefixEnd_5797192 2976745942399587693339205 := by
  unfold tailWord_5797192
  simp only [CollatzResearch.WordTrace]
  refine ⟨105720481406885470207144915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140960641875847293609526553 105720481406885470207144915)
  ·
    refine ⟨158580722110328205310717373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105720481406885470207144915 158580722110328205310717373)
    ·
      refine ⟨59467770791373076991519015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158580722110328205310717373 59467770791373076991519015)
      ·
        refine ⟨89201656187059615487278523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59467770791373076991519015 89201656187059615487278523)
        ·
          refine ⟨133802484280589423230917785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89201656187059615487278523 133802484280589423230917785)
          ·
            refine ⟨100351863210442067423188339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133802484280589423230917785 100351863210442067423188339)
            ·
              refine ⟨150527794815663101134782509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100351863210442067423188339 150527794815663101134782509)
              ·
                refine ⟨56447923055873662925543441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150527794815663101134782509 56447923055873662925543441)
                ·
                  refine ⟨42335942291905247194157581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56447923055873662925543441 42335942291905247194157581)
                  ·
                    refine ⟨15875978359464467697809093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42335942291905247194157581 15875978359464467697809093)
                    ·
                      refine ⟨2976745942399587693339205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15875978359464467697809093 2976745942399587693339205)
                      ·
                        rfl

theorem cell23_5797192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_5797192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797192 prefixEnd_5797192 := by exact prefixLift 5797192
  have htrace : WordTrace (prefixWord ++ tailWord_5797192) baseStart_5797192 baseEnd_5797192 := by
    simpa [prefixWord, tailWord_5797192, baseEnd_5797192] using wordTrace_append hprefix tailTrace_5797192
  have hstable : (prefixWord ++ tailWord_5797192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797192).length < 2 ^ (prefixWord ++ tailWord_5797192).sum := by decide
  have hdescent : baseEnd_5797192 < baseStart_5797192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797197 : List Nat := [1, 6, 1, 3, 1, 2, 2, 1, 2, 4]
def baseStart_5797197 : Nat := 118140960795 + 5797197 * 2 ^ 59
def prefixEnd_5797197 : Nat := 4983230072969 + 3 ^ 40 * 5797197 * 2
def baseEnd_5797197 : Nat := 992249503267620057925561

theorem tailTrace_5797197 : CollatzResearch.WordTrace tailWord_5797197 prefixEnd_5797197 992249503267620057925561 := by
  unfold tailWord_5797197
  simp only [CollatzResearch.WordTrace]
  refine ⟨211441145178752826268221845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140960763452501884178814563 211441145178752826268221845)
  ·
    refine ⟨9911303680254038731322899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 211441145178752826268221845 9911303680254038731322899)
    ·
      refine ⟨14866955520381058096984349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9911303680254038731322899 14866955520381058096984349)
      ·
        refine ⟨5575108320142896786369131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14866955520381058096984349 5575108320142896786369131)
        ·
          refine ⟨8362662480214345179553697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5575108320142896786369131 8362662480214345179553697)
          ·
            refine ⟨6271996860160758884665273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8362662480214345179553697 6271996860160758884665273)
            ·
              refine ⟨4703997645120569163498955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6271996860160758884665273 4703997645120569163498955)
              ·
                refine ⟨7055996467680853745248433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4703997645120569163498955 7055996467680853745248433)
                ·
                  refine ⟨5291997350760640308936325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7055996467680853745248433 5291997350760640308936325)
                  ·
                    refine ⟨992249503267620057925561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5291997350760640308936325 992249503267620057925561)
                    ·
                      rfl

theorem cell23_5797197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_5797197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797197 prefixEnd_5797197 := by exact prefixLift 5797197
  have htrace : WordTrace (prefixWord ++ tailWord_5797197) baseStart_5797197 baseEnd_5797197 := by
    simpa [prefixWord, tailWord_5797197, baseEnd_5797197] using wordTrace_append hprefix tailTrace_5797197
  have hstable : (prefixWord ++ tailWord_5797197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797197).length < 2 ^ (prefixWord ++ tailWord_5797197).sum := by decide
  have hdescent : baseEnd_5797197 < baseStart_5797197 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797202 : List Nat := [3, 2, 2, 1, 1, 1, 1, 3, 1, 8]
def baseStart_5797202 : Nat := 118140960795 + 5797202 * 2 ^ 59
def prefixEnd_5797202 : Nat := 4983230072969 + 3 ^ 40 * 5797202 * 2
def baseEnd_5797202 : Nat := 992250359068710884738053

theorem tailTrace_5797202 : CollatzResearch.WordTrace tailWord_5797202 prefixEnd_5797202 992250359068710884738053 := by
  unfold tailWord_5797202
  simp only [CollatzResearch.WordTrace]
  refine ⟨52860331885933678030538465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140960885029156474748102573 52860331885933678030538465)
  ·
    refine ⟨39645248914450258522903849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52860331885933678030538465 39645248914450258522903849)
    ·
      refine ⟨29733936685837693892177887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39645248914450258522903849 29733936685837693892177887)
      ·
        refine ⟨44600905028756540838266831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29733936685837693892177887 44600905028756540838266831)
        ·
          refine ⟨66901357543134811257400247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44600905028756540838266831 66901357543134811257400247)
          ·
            refine ⟨100352036314702216886100371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66901357543134811257400247 100352036314702216886100371)
            ·
              refine ⟨150528054472053325329150557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100352036314702216886100371 150528054472053325329150557)
              ·
                refine ⟨56448020427019996998431459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150528054472053325329150557 56448020427019996998431459)
                ·
                  refine ⟨84672030640529995497647189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56448020427019996998431459 84672030640529995497647189)
                  ·
                    refine ⟨992250359068710884738053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 84672030640529995497647189 992250359068710884738053)
                    ·
                      rfl

theorem cell23_5797202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_5797202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797202 prefixEnd_5797202 := by exact prefixLift 5797202
  have htrace : WordTrace (prefixWord ++ tailWord_5797202) baseStart_5797202 baseEnd_5797202 := by
    simpa [prefixWord, tailWord_5797202, baseEnd_5797202] using wordTrace_append hprefix tailTrace_5797202
  have hstable : (prefixWord ++ tailWord_5797202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797202).length < 2 ^ (prefixWord ++ tailWord_5797202).sum := by decide
  have hdescent : baseEnd_5797202 < baseStart_5797202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797229 : List Nat := [1, 5, 1, 1, 1, 3, 2, 1, 2, 1, 5]
def baseStart_5797229 : Nat := 118140960795 + 5797229 * 2 ^ 59
def prefixEnd_5797229 : Nat := 4983230072969 + 3 ^ 40 * 5797229 * 2
def baseEnd_5797229 : Nat := 2976764941183804048576535

theorem tailTrace_5797229 : CollatzResearch.WordTrace tailWord_5797229 prefixEnd_5797229 2976764941183804048576535 := by
  unfold tailWord_5797229
  simp only [CollatzResearch.WordTrace]
  refine ⟨211442312314636895733386741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140961541543091263822257827 211442312314636895733386741)
  ·
    refine ⟨19822716779497208975005007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 211442312314636895733386741 19822716779497208975005007)
    ·
      refine ⟨29734075169245813462507511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19822716779497208975005007 29734075169245813462507511)
      ·
        refine ⟨44601112753868720193761267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29734075169245813462507511 44601112753868720193761267)
        ·
          refine ⟨66901669130803080290641901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44601112753868720193761267 66901669130803080290641901)
          ·
            refine ⟨25088125924051155108990713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66901669130803080290641901 25088125924051155108990713)
            ·
              refine ⟨18816094443038366331743035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25088125924051155108990713 18816094443038366331743035)
              ·
                refine ⟨28224141664557549497614553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18816094443038366331743035 28224141664557549497614553)
                ·
                  refine ⟨21168106248418162123210915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28224141664557549497614553 21168106248418162123210915)
                  ·
                    refine ⟨31752159372627243184816373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21168106248418162123210915 31752159372627243184816373)
                    ·
                      refine ⟨2976764941183804048576535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31752159372627243184816373 2976764941183804048576535)
                      ·
                        rfl

theorem cell23_5797229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_5797229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797229 prefixEnd_5797229 := by exact prefixLift 5797229
  have htrace : WordTrace (prefixWord ++ tailWord_5797229) baseStart_5797229 baseEnd_5797229 := by
    simpa [prefixWord, tailWord_5797229, baseEnd_5797229] using wordTrace_append hprefix tailTrace_5797229
  have hstable : (prefixWord ++ tailWord_5797229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797229).length < 2 ^ (prefixWord ++ tailWord_5797229).sum := by decide
  have hdescent : baseEnd_5797229 < baseStart_5797229 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797243 : List Nat := [1, 1, 1, 1, 1, 6, 4, 2, 2, 2, 2]
def baseStart_5797243 : Nat := 118140960795 + 5797243 * 2 ^ 59
def prefixEnd_5797243 : Nat := 4983230072969 + 3 ^ 40 * 5797243 * 2
def baseEnd_5797243 : Nat := 2976772129912966993801471

theorem tailTrace_5797243 : CollatzResearch.WordTrace tailWord_5797243 prefixEnd_5797243 2976772129912966993801471 := by
  unfold tailWord_5797243
  simp only [CollatzResearch.WordTrace]
  refine ⟨211442822936586176124396383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140961881957724117416264255 211442822936586176124396383)
  ·
    refine ⟨317164234404879264186594575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211442822936586176124396383 317164234404879264186594575)
    ·
      refine ⟨475746351607318896279891863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317164234404879264186594575 475746351607318896279891863)
      ·
        refine ⟨713619527410978344419837795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475746351607318896279891863 713619527410978344419837795)
        ·
          refine ⟨1070429291116467516629756693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 713619527410978344419837795 1070429291116467516629756693)
          ·
            refine ⟨50176373021084414842019845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1070429291116467516629756693 50176373021084414842019845)
            ·
              refine ⟨9408069941453327782878721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50176373021084414842019845 9408069941453327782878721)
              ·
                refine ⟨7056052456089995837159041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9408069941453327782878721 7056052456089995837159041)
                ·
                  refine ⟨5292039342067496877869281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7056052456089995837159041 5292039342067496877869281)
                  ·
                    refine ⟨3969029506550622658401961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5292039342067496877869281 3969029506550622658401961)
                    ·
                      refine ⟨2976772129912966993801471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3969029506550622658401961 2976772129912966993801471)
                      ·
                        rfl

theorem cell23_5797243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 2, 2, 2, 2].length) (baseStart_5797243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797243 prefixEnd_5797243 := by exact prefixLift 5797243
  have htrace : WordTrace (prefixWord ++ tailWord_5797243) baseStart_5797243 baseEnd_5797243 := by
    simpa [prefixWord, tailWord_5797243, baseEnd_5797243] using wordTrace_append hprefix tailTrace_5797243
  have hstable : (prefixWord ++ tailWord_5797243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797243).length < 2 ^ (prefixWord ++ tailWord_5797243).sum := by decide
  have hdescent : baseEnd_5797243 < baseStart_5797243 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797259 : List Nat := [1, 1, 1, 1, 4, 3, 3, 1, 2, 3, 3]
def baseStart_5797259 : Nat := 118140960795 + 5797259 * 2 ^ 59
def prefixEnd_5797259 : Nat := 4983230072969 + 3 ^ 40 * 5797259 * 2
def baseEnd_5797259 : Nat := 2976780345603438931201397

theorem tailTrace_5797259 : CollatzResearch.WordTrace tailWord_5797259 prefixEnd_5797259 2976780345603438931201397 := by
  unfold tailWord_5797259
  simp only [CollatzResearch.WordTrace]
  refine ⟨211443406504528210856978831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140962271003018807237985887 211443406504528210856978831)
  ·
    refine ⟨317165109756792316285468247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211443406504528210856978831 317165109756792316285468247)
    ·
      refine ⟨475747664635188474428202371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317165109756792316285468247 475747664635188474428202371)
      ·
        refine ⟨713621496952782711642303557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475747664635188474428202371 713621496952782711642303557)
        ·
          refine ⟨133804030678646758432931917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 713621496952782711642303557 133804030678646758432931917)
          ·
            refine ⟨50176511504492534412349469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133804030678646758432931917 50176511504492534412349469)
            ·
              refine ⟨18816191814184700404631051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50176511504492534412349469 18816191814184700404631051)
              ·
                refine ⟨28224287721277050606946577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18816191814184700404631051 28224287721277050606946577)
                ·
                  refine ⟨21168215790957787955209933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28224287721277050606946577 21168215790957787955209933)
                  ·
                    refine ⟨7938080921609170483203725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21168215790957787955209933 7938080921609170483203725)
                    ·
                      refine ⟨2976780345603438931201397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7938080921609170483203725 2976780345603438931201397)
                      ·
                        rfl

theorem cell23_5797259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 3, 3].length) (baseStart_5797259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797259 prefixEnd_5797259 := by exact prefixLift 5797259
  have htrace : WordTrace (prefixWord ++ tailWord_5797259) baseStart_5797259 baseEnd_5797259 := by
    simpa [prefixWord, tailWord_5797259, baseEnd_5797259] using wordTrace_append hprefix tailTrace_5797259
  have hstable : (prefixWord ++ tailWord_5797259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797259).length < 2 ^ (prefixWord ++ tailWord_5797259).sum := by decide
  have hdescent : baseEnd_5797259 < baseStart_5797259 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797279 : List Nat := [1, 1, 2, 5, 1, 3, 1, 1, 1, 7]
def baseStart_5797279 : Nat := 118140960795 + 5797279 * 2 ^ 59
def prefixEnd_5797279 : Nat := 4983230072969 + 3 ^ 40 * 5797279 * 2
def baseEnd_5797279 : Nat := 992263538405509617650435

theorem tailTrace_5797279 : CollatzResearch.WordTrace tailWord_5797279 prefixEnd_5797279 992263538405509617650435 := by
  unfold tailWord_5797279
  simp only [CollatzResearch.WordTrace]
  refine ⟨211444135964455754272706891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140962757309637169515137927 211444135964455754272706891)
  ·
    refine ⟨317166203946683631409060337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211444135964455754272706891 317166203946683631409060337)
    ·
      refine ⟨237874652960012723556795253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317166203946683631409060337 237874652960012723556795253)
      ·
        refine ⟨22300748715001192833449555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 237874652960012723556795253 22300748715001192833449555)
        ·
          refine ⟨33451123072501789250174333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22300748715001192833449555 33451123072501789250174333)
          ·
            refine ⟨12544171152188170968815375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33451123072501789250174333 12544171152188170968815375)
            ·
              refine ⟨18816256728282256453223063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12544171152188170968815375 18816256728282256453223063)
              ·
                refine ⟨28224385092423384679834595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18816256728282256453223063 28224385092423384679834595)
                ·
                  refine ⟨42336577638635077019751893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28224385092423384679834595 42336577638635077019751893)
                  ·
                    refine ⟨992263538405509617650435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42336577638635077019751893 992263538405509617650435)
                    ·
                      rfl

theorem cell23_5797279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 7].length) (baseStart_5797279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797279 prefixEnd_5797279 := by exact prefixLift 5797279
  have htrace : WordTrace (prefixWord ++ tailWord_5797279) baseStart_5797279 baseEnd_5797279 := by
    simpa [prefixWord, tailWord_5797279, baseEnd_5797279] using wordTrace_append hprefix tailTrace_5797279
  have hstable : (prefixWord ++ tailWord_5797279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797279).length < 2 ^ (prefixWord ++ tailWord_5797279).sum := by decide
  have hdescent : baseEnd_5797279 < baseStart_5797279 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797299 : List Nat := [1, 1, 1, 2, 3, 1, 1, 6, 2, 1, 4]
def baseStart_5797299 : Nat := 118140960795 + 5797299 * 2 ^ 59
def prefixEnd_5797299 : Nat := 4983230072969 + 3 ^ 40 * 5797299 * 2
def baseEnd_5797299 : Nat := 2976800884829618774701213

theorem tailTrace_5797299 : CollatzResearch.WordTrace tailWord_5797299 prefixEnd_5797299 2976800884829618774701213 := by
  unfold tailWord_5797299
  simp only [CollatzResearch.WordTrace]
  refine ⟨211444865424383297688434951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140963243616255531792289967 211444865424383297688434951)
  ·
    refine ⟨317167298136574946532652427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211444865424383297688434951 317167298136574946532652427)
    ·
      refine ⟨475750947204862419798978641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317167298136574946532652427 475750947204862419798978641)
      ·
        refine ⟨356813210403646814849233981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 475750947204862419798978641 356813210403646814849233981)
        ·
          refine ⟨133804953901367555568462743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 356813210403646814849233981 133804953901367555568462743)
          ·
            refine ⟨200707430852051333352694115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133804953901367555568462743 200707430852051333352694115)
            ·
              refine ⟨301061146278077000029041173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200707430852051333352694115 301061146278077000029041173)
              ·
                refine ⟨14112241231784859376361305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 301061146278077000029041173 14112241231784859376361305)
                ·
                  refine ⟨10584180923838644532270979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14112241231784859376361305 10584180923838644532270979)
                  ·
                    refine ⟨15876271385757966798406469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10584180923838644532270979 15876271385757966798406469)
                    ·
                      refine ⟨2976800884829618774701213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15876271385757966798406469 2976800884829618774701213)
                      ·
                        rfl

theorem cell23_5797299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 2, 1, 4].length) (baseStart_5797299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797299 prefixEnd_5797299 := by exact prefixLift 5797299
  have htrace : WordTrace (prefixWord ++ tailWord_5797299) baseStart_5797299 baseEnd_5797299 := by
    simpa [prefixWord, tailWord_5797299, baseEnd_5797299] using wordTrace_append hprefix tailTrace_5797299
  have hstable : (prefixWord ++ tailWord_5797299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797299).length < 2 ^ (prefixWord ++ tailWord_5797299).sum := by decide
  have hdescent : baseEnd_5797299 < baseStart_5797299 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797316 : List Nat := [2, 3, 3, 2, 1, 1, 1, 2, 1, 3, 4]
def baseStart_5797316 : Nat := 118140960795 + 5797316 * 2 ^ 59
def prefixEnd_5797316 : Nat := 4983230072969 + 3 ^ 40 * 5797316 * 2
def baseEnd_5797316 : Nat := 2976809614000745208188635

theorem tailTrace_5797316 : CollatzResearch.WordTrace tailWord_5797316 prefixEnd_5797316 2976809614000745208188635 := by
  unfold tailWord_5797316
  simp only [CollatzResearch.WordTrace]
  refine ⟨105722742732660854795901901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140963656976881139727869201 105722742732660854795901901)
  ·
    refine ⟨39646028524747820548463213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105722742732660854795901901 39646028524747820548463213)
    ·
      refine ⟨14867260696780432705673705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39646028524747820548463213 14867260696780432705673705)
      ·
        refine ⟨11150445522585324529255279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14867260696780432705673705 11150445522585324529255279)
        ·
          refine ⟨16725668283877986793882919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11150445522585324529255279 16725668283877986793882919)
          ·
            refine ⟨25088502425816980190824379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16725668283877986793882919 25088502425816980190824379)
            ·
              refine ⟨37632753638725470286236569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25088502425816980190824379 37632753638725470286236569)
              ·
                refine ⟨28224565229044102714677427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37632753638725470286236569 28224565229044102714677427)
                ·
                  refine ⟨42336847843566154072016141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28224565229044102714677427 42336847843566154072016141)
                  ·
                    refine ⟨15876317941337307777006053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42336847843566154072016141 15876317941337307777006053)
                    ·
                      refine ⟨2976809614000745208188635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15876317941337307777006053 2976809614000745208188635)
                      ·
                        rfl

theorem cell23_5797316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_5797316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797316 prefixEnd_5797316 := by exact prefixLift 5797316
  have htrace : WordTrace (prefixWord ++ tailWord_5797316) baseStart_5797316 baseEnd_5797316 := by
    simpa [prefixWord, tailWord_5797316, baseEnd_5797316] using wordTrace_append hprefix tailTrace_5797316
  have hstable : (prefixWord ++ tailWord_5797316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797316).length < 2 ^ (prefixWord ++ tailWord_5797316).sum := by decide
  have hdescent : baseEnd_5797316 < baseStart_5797316 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797319 : List Nat := [1, 1, 4, 1, 1, 3, 1, 1, 3, 4, 3]
def baseStart_5797319 : Nat := 118140960795 + 5797319 * 2 ^ 59
def prefixEnd_5797319 : Nat := 4983230072969 + 3 ^ 40 * 5797319 * 2
def baseEnd_5797319 : Nat := 2976811154442708696451121

theorem tailTrace_5797319 : CollatzResearch.WordTrace tailWord_5797319 prefixEnd_5797319 2976811154442708696451121 := by
  unfold tailWord_5797319
  simp only [CollatzResearch.WordTrace]
  refine ⟨211445594884310841104163011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140963729922873894069442007 211445594884310841104163011)
  ·
    refine ⟨317168392326466261656244517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211445594884310841104163011 317168392326466261656244517)
    ·
      refine ⟨59469073561212424060545847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 317168392326466261656244517 59469073561212424060545847)
      ·
        refine ⟨89203610341818636090818771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59469073561212424060545847 89203610341818636090818771)
        ·
          refine ⟨133805415512727954136228157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89203610341818636090818771 133805415512727954136228157)
          ·
            refine ⟨50177030817272982801085559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133805415512727954136228157 50177030817272982801085559)
            ·
              refine ⟨75265546225909474201628339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50177030817272982801085559 75265546225909474201628339)
              ·
                refine ⟨112898319338864211302442509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75265546225909474201628339 112898319338864211302442509)
                ·
                  refine ⟨42336869752074079238415941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112898319338864211302442509 42336869752074079238415941)
                  ·
                    refine ⟨7938163078513889857202989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42336869752074079238415941 7938163078513889857202989)
                    ·
                      refine ⟨2976811154442708696451121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7938163078513889857202989 2976811154442708696451121)
                      ·
                        rfl

theorem cell23_5797319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 4, 3].length) (baseStart_5797319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797319 prefixEnd_5797319 := by exact prefixLift 5797319
  have htrace : WordTrace (prefixWord ++ tailWord_5797319) baseStart_5797319 baseEnd_5797319 := by
    simpa [prefixWord, tailWord_5797319, baseEnd_5797319] using wordTrace_append hprefix tailTrace_5797319
  have hstable : (prefixWord ++ tailWord_5797319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797319).length < 2 ^ (prefixWord ++ tailWord_5797319).sum := by decide
  have hdescent : baseEnd_5797319 < baseStart_5797319 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797326 : List Nat := [4, 1, 1, 1, 2, 1, 4, 2, 3, 4]
def baseStart_5797326 : Nat := 118140960795 + 5797326 * 2 ^ 59
def prefixEnd_5797326 : Nat := 4983230072969 + 3 ^ 40 * 5797326 * 2
def baseEnd_5797326 : Nat := 992271582935763389687863

theorem tailTrace_5797326 : CollatzResearch.WordTrace tailWord_5797326 prefixEnd_5797326 992271582935763389687863 := by
  unfold tailWord_5797326
  simp only [CollatzResearch.WordTrace]
  refine ⟨26430731274410685162458479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140963900130190320866445221 26430731274410685162458479)
  ·
    refine ⟨39646096911616027743687719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26430731274410685162458479 39646096911616027743687719)
    ·
      refine ⟨59469145367424041615531579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39646096911616027743687719 59469145367424041615531579)
      ·
        refine ⟨89203718051136062423297369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59469145367424041615531579 89203718051136062423297369)
        ·
          refine ⟨66902788538352046817473027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89203718051136062423297369 66902788538352046817473027)
          ·
            refine ⟨100354182807528070226209541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66902788538352046817473027 100354182807528070226209541)
            ·
              refine ⟨18816409276411513167414289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100354182807528070226209541 18816409276411513167414289)
              ·
                refine ⟨14112306957308634875560717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18816409276411513167414289 14112306957308634875560717)
                ·
                  refine ⟨5292115108990738078335269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14112306957308634875560717 5292115108990738078335269)
                  ·
                    refine ⟨992271582935763389687863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5292115108990738078335269 992271582935763389687863)
                    ·
                      rfl

theorem cell23_5797326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 3, 4].length) (baseStart_5797326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797326 prefixEnd_5797326 := by exact prefixLift 5797326
  have htrace : WordTrace (prefixWord ++ tailWord_5797326) baseStart_5797326 baseEnd_5797326 := by
    simpa [prefixWord, tailWord_5797326, baseEnd_5797326] using wordTrace_append hprefix tailTrace_5797326
  have hstable : (prefixWord ++ tailWord_5797326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797326).length < 2 ^ (prefixWord ++ tailWord_5797326).sum := by decide
  have hdescent : baseEnd_5797326 < baseStart_5797326 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797360 : List Nat := [2, 1, 1, 1, 3, 5, 3, 2, 1, 4]
def baseStart_5797360 : Nat := 118140960795 + 5797360 * 2 ^ 59
def prefixEnd_5797360 : Nat := 4983230072969 + 3 ^ 40 * 5797360 * 2
def baseEnd_5797360 : Nat := 992277402383181012012811

theorem tailTrace_5797360 : CollatzResearch.WordTrace tailWord_5797360 prefixEnd_5797360 992277402383181012012811 := by
  unfold tailWord_5797360
  simp only [CollatzResearch.WordTrace]
  refine ⟨105723545138581152553202767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140964726851441536737603689 105723545138581152553202767)
  ·
    refine ⟨158585317707871728829804151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105723545138581152553202767 158585317707871728829804151)
    ·
      refine ⟨237877976561807593244706227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158585317707871728829804151 237877976561807593244706227)
      ·
        refine ⟨356816964842711389867059341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237877976561807593244706227 356816964842711389867059341)
        ·
          refine ⟨133806361816016771200147253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 356816964842711389867059341 133806361816016771200147253)
          ·
            refine ⟨12544346420251572300013805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 133806361816016771200147253 12544346420251572300013805)
            ·
              refine ⟨4704129907594339612505177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12544346420251572300013805 4704129907594339612505177)
              ·
                refine ⟨3528097430695754709378883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4704129907594339612505177 3528097430695754709378883)
                ·
                  refine ⟨5292146146043632064068325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3528097430695754709378883 5292146146043632064068325)
                  ·
                    refine ⟨992277402383181012012811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5292146146043632064068325 992277402383181012012811)
                    ·
                      rfl

theorem cell23_5797360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 2, 1, 4].length) (baseStart_5797360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797360 prefixEnd_5797360 := by exact prefixLift 5797360
  have htrace : WordTrace (prefixWord ++ tailWord_5797360) baseStart_5797360 baseEnd_5797360 := by
    simpa [prefixWord, tailWord_5797360, baseEnd_5797360] using wordTrace_append hprefix tailTrace_5797360
  have hstable : (prefixWord ++ tailWord_5797360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797360).length < 2 ^ (prefixWord ++ tailWord_5797360).sum := by decide
  have hdescent : baseEnd_5797360 < baseStart_5797360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797369 : List Nat := [1, 2, 1, 3, 1, 2, 1, 4, 3, 5]
def baseStart_5797369 : Nat := 118140960795 + 5797369 * 2 ^ 59
def prefixEnd_5797369 : Nat := 4983230072969 + 3 ^ 40 * 5797369 * 2
def baseEnd_5797369 : Nat := 992278942825144500275297

theorem tailTrace_5797369 : CollatzResearch.WordTrace tailWord_5797369 prefixEnd_5797369 992278942825144500275297 := by
  unfold tailWord_5797369
  simp only [CollatzResearch.WordTrace]
  refine ⟨211447418534129699643483161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140964945689419799762322107 211447418534129699643483161)
  ·
    refine ⟨158585563900597274732612371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211447418534129699643483161 158585563900597274732612371)
    ·
      refine ⟨237878345850895912098918557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158585563900597274732612371 237878345850895912098918557)
      ·
        refine ⟨89204379694085967037094459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 237878345850895912098918557 89204379694085967037094459)
        ·
          refine ⟨133806569541128950555641689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89204379694085967037094459 133806569541128950555641689)
          ·
            refine ⟨100354927155846712916731267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133806569541128950555641689 100354927155846712916731267)
            ·
              refine ⟨150532390733770069375096901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100354927155846712916731267 150532390733770069375096901)
              ·
                refine ⟨28224823262581888007830669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 150532390733770069375096901 28224823262581888007830669)
                ·
                  refine ⟨10584308723468208002936501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28224823262581888007830669 10584308723468208002936501)
                  ·
                    refine ⟨992278942825144500275297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10584308723468208002936501 992278942825144500275297)
                    ·
                      rfl

theorem cell23_5797369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 3, 5].length) (baseStart_5797369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797369 prefixEnd_5797369 := by exact prefixLift 5797369
  have htrace : WordTrace (prefixWord ++ tailWord_5797369) baseStart_5797369 baseEnd_5797369 := by
    simpa [prefixWord, tailWord_5797369, baseEnd_5797369] using wordTrace_append hprefix tailTrace_5797369
  have hstable : (prefixWord ++ tailWord_5797369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797369).length < 2 ^ (prefixWord ++ tailWord_5797369).sum := by decide
  have hdescent : baseEnd_5797369 < baseStart_5797369 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797373 : List Nat := [1, 4, 1, 1, 1, 6, 2, 1, 6]
def baseStart_5797373 : Nat := 118140960795 + 5797373 * 2 ^ 59
def prefixEnd_5797373 : Nat := 4983230072969 + 3 ^ 40 * 5797373 * 2
def baseEnd_5797373 : Nat := 330759875822005720575097

theorem tailTrace_5797373 : CollatzResearch.WordTrace tailWord_5797373 prefixEnd_5797373 330759875822005720575097 := by
  unfold tailWord_5797373
  simp only [CollatzResearch.WordTrace]
  refine ⟨211447564426115208326628773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140965042950743472217752515 211447564426115208326628773)
  ·
    refine ⟨39646418329896601561242895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 211447564426115208326628773 39646418329896601561242895)
    ·
      refine ⟨59469627494844902341864343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39646418329896601561242895 59469627494844902341864343)
      ·
        refine ⟨89204441242267353512796515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59469627494844902341864343 89204441242267353512796515)
        ·
          refine ⟨133806661863401030269194773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89204441242267353512796515 133806661863401030269194773)
          ·
            refine ⟨6272187274846923293868505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 133806661863401030269194773 6272187274846923293868505)
            ·
              refine ⟨4704140456135192470401379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6272187274846923293868505 4704140456135192470401379)
              ·
                refine ⟨7056210684202788705602069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4704140456135192470401379 7056210684202788705602069)
                ·
                  refine ⟨330759875822005720575097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7056210684202788705602069 330759875822005720575097)
                  ·
                    rfl

theorem cell23_5797373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 1, 6].length) (baseStart_5797373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797373 prefixEnd_5797373 := by exact prefixLift 5797373
  have htrace : WordTrace (prefixWord ++ tailWord_5797373) baseStart_5797373 baseEnd_5797373 := by
    simpa [prefixWord, tailWord_5797373, baseEnd_5797373] using wordTrace_append hprefix tailTrace_5797373
  have hstable : (prefixWord ++ tailWord_5797373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797373).length < 2 ^ (prefixWord ++ tailWord_5797373).sum := by decide
  have hdescent : baseEnd_5797373 < baseStart_5797373 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797386 : List Nat := [3, 1, 2, 2, 2, 3, 1, 1, 3, 5]
def baseStart_5797386 : Nat := 118140960795 + 5797386 * 2 ^ 59
def prefixEnd_5797386 : Nat := 4983230072969 + 3 ^ 40 * 5797386 * 2
def baseEnd_5797386 : Nat := 992281852548853311437771

theorem tailTrace_5797386 : CollatzResearch.WordTrace tailWord_5797386 prefixEnd_5797386 992281852548853311437771 := by
  unfold tailWord_5797386
  simp only [CollatzResearch.WordTrace]
  refine ⟨52862009643767027886713003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140965359050045407697901341 52862009643767027886713003)
  ·
    refine ⟨79293014465650541830069505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52862009643767027886713003 79293014465650541830069505)
    ·
      refine ⟨59469760849237906372552129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79293014465650541830069505 59469760849237906372552129)
      ·
        refine ⟨44602320636928429779414097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59469760849237906372552129 44602320636928429779414097)
        ·
          refine ⟨33451740477696322334560573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44602320636928429779414097 33451740477696322334560573)
          ·
            refine ⟨12544402679136120875460215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33451740477696322334560573 12544402679136120875460215)
            ·
              refine ⟨18816604018704181313190323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12544402679136120875460215 18816604018704181313190323)
              ·
                refine ⟨28224906028056271969785485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18816604018704181313190323 28224906028056271969785485)
                ·
                  refine ⟨10584339760521101988669557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28224906028056271969785485 10584339760521101988669557)
                  ·
                    refine ⟨992281852548853311437771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10584339760521101988669557 992281852548853311437771)
                    ·
                      rfl

theorem cell23_5797386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 3, 5].length) (baseStart_5797386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797386 prefixEnd_5797386 := by exact prefixLift 5797386
  have htrace : WordTrace (prefixWord ++ tailWord_5797386) baseStart_5797386 baseEnd_5797386 := by
    simpa [prefixWord, tailWord_5797386, baseEnd_5797386] using wordTrace_append hprefix tailTrace_5797386
  have hstable : (prefixWord ++ tailWord_5797386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797386).length < 2 ^ (prefixWord ++ tailWord_5797386).sum := by decide
  have hdescent : baseEnd_5797386 < baseStart_5797386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797393 : List Nat := [1, 2, 2, 1, 1, 2, 6, 1, 2, 3, 2]
def baseStart_5797393 : Nat := 118140960795 + 5797393 * 2 ^ 59
def prefixEnd_5797393 : Nat := 4983230072969 + 3 ^ 40 * 5797393 * 2
def baseEnd_5797393 : Nat := 2976849152011141406925781

theorem tailTrace_5797393 : CollatzResearch.WordTrace tailWord_5797393 prefixEnd_5797393 2976849152011141406925781 := by
  unfold tailWord_5797393
  simp only [CollatzResearch.WordTrace]
  refine ⟨211448293886042751742356833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140965529257361834494904555 211448293886042751742356833)
  ·
    refine ⟨158586220414532063806767625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211448293886042751742356833 158586220414532063806767625)
    ·
      refine ⟨118939665310899047855075719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158586220414532063806767625 118939665310899047855075719)
      ·
        refine ⟨178409497966348571782613579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118939665310899047855075719 178409497966348571782613579)
        ·
          refine ⟨267614246949522857673920369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178409497966348571782613579 267614246949522857673920369)
          ·
            refine ⟨200710685212142143255440277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267614246949522857673920369 200710685212142143255440277)
            ·
              refine ⟨9408313369319162965098763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 200710685212142143255440277 9408313369319162965098763)
              ·
                refine ⟨14112470053978744447648145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9408313369319162965098763 14112470053978744447648145)
                ·
                  refine ⟨10584352540484058335736109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14112470053978744447648145 10584352540484058335736109)
                  ·
                    refine ⟨3969132202681521875901041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10584352540484058335736109 3969132202681521875901041)
                    ·
                      refine ⟨2976849152011141406925781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3969132202681521875901041 2976849152011141406925781)
                      ·
                        rfl

theorem cell23_5797393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 3, 2].length) (baseStart_5797393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797393 prefixEnd_5797393 := by exact prefixLift 5797393
  have htrace : WordTrace (prefixWord ++ tailWord_5797393) baseStart_5797393 baseEnd_5797393 := by
    simpa [prefixWord, tailWord_5797393, baseEnd_5797393] using wordTrace_append hprefix tailTrace_5797393
  have hstable : (prefixWord ++ tailWord_5797393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797393).length < 2 ^ (prefixWord ++ tailWord_5797393).sum := by decide
  have hdescent : baseEnd_5797393 < baseStart_5797393 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797433 : List Nat := [1, 2, 1, 5, 1, 2, 2, 3, 2, 4]
def baseStart_5797433 : Nat := 118140960795 + 5797433 * 2 ^ 59
def prefixEnd_5797433 : Nat := 4983230072969 + 3 ^ 40 * 5797433 * 2
def baseEnd_5797433 : Nat := 992289897079107083475199

theorem tailTrace_5797433 : CollatzResearch.WordTrace tailWord_5797433 prefixEnd_5797433 992289897079107083475199 := by
  unfold tailWord_5797433
  simp only [CollatzResearch.WordTrace]
  refine ⟨211449752805897838573812953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140966501870598559049208635 211449752805897838573812953)
  ·
    refine ⟨158587314604423378930359715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211449752805897838573812953 158587314604423378930359715)
    ·
      refine ⟨237880971906635068395539573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158587314604423378930359715 237880971906635068395539573)
      ·
        refine ⟨22301341116247037662081835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 237880971906635068395539573 22301341116247037662081835)
        ·
          refine ⟨33452011674370556493122753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22301341116247037662081835 33452011674370556493122753)
          ·
            refine ⟨25089008755777917369842065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33452011674370556493122753 25089008755777917369842065)
            ·
              refine ⟨18816756566833438027381549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25089008755777917369842065 18816756566833438027381549)
              ·
                refine ⟨7056283712562539260268081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18816756566833438027381549 7056283712562539260268081)
                ·
                  refine ⟨5292212784421904445201061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7056283712562539260268081 5292212784421904445201061)
                  ·
                    refine ⟨992289897079107083475199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5292212784421904445201061 992289897079107083475199)
                    ·
                      rfl

theorem cell23_5797433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 3, 2, 4].length) (baseStart_5797433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797433 prefixEnd_5797433 := by exact prefixLift 5797433
  have htrace : WordTrace (prefixWord ++ tailWord_5797433) baseStart_5797433 baseEnd_5797433 := by
    simpa [prefixWord, tailWord_5797433, baseEnd_5797433] using wordTrace_append hprefix tailTrace_5797433
  have hstable : (prefixWord ++ tailWord_5797433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797433).length < 2 ^ (prefixWord ++ tailWord_5797433).sum := by decide
  have hdescent : baseEnd_5797433 < baseStart_5797433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797456 : List Nat := [2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 3]
def baseStart_5797456 : Nat := 118140960795 + 5797456 * 2 ^ 59
def prefixEnd_5797456 : Nat := 4983230072969 + 3 ^ 40 * 5797456 * 2
def baseEnd_5797456 : Nat := 2976881501292374660437991

theorem tailTrace_5797456 : CollatzResearch.WordTrace tailWord_5797456 prefixEnd_5797456 2976881501292374660437991 := by
  unfold tailWord_5797456
  simp only [CollatzResearch.WordTrace]
  refine ⟨105725295842407256750950111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140967061123209675667933481 105725295842407256750950111)
  ·
    refine ⟨158587943763610885126425167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105725295842407256750950111 158587943763610885126425167)
    ·
      refine ⟨237881915645416327689637751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158587943763610885126425167 237881915645416327689637751)
      ·
        refine ⟨356822873468124491534456627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237881915645416327689637751 356822873468124491534456627)
        ·
          refine ⟨535234310202186737301684941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356822873468124491534456627 535234310202186737301684941)
          ·
            refine ⟨200712866325820026488131853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 535234310202186737301684941 200712866325820026488131853)
            ·
              refine ⟨75267324872182509933049445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 200712866325820026488131853 75267324872182509933049445)
              ·
                refine ⟨14112623413534220612446771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75267324872182509933049445 14112623413534220612446771)
                ·
                  refine ⟨21168935120301330918670157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14112623413534220612446771 21168935120301330918670157)
                  ·
                    refine ⟨7938350670112999094501309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21168935120301330918670157 7938350670112999094501309)
                    ·
                      refine ⟨2976881501292374660437991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7938350670112999094501309 2976881501292374660437991)
                      ·
                        rfl

theorem cell23_5797456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 3].length) (baseStart_5797456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797456 prefixEnd_5797456 := by exact prefixLift 5797456
  have htrace : WordTrace (prefixWord ++ tailWord_5797456) baseStart_5797456 baseEnd_5797456 := by
    simpa [prefixWord, tailWord_5797456, baseEnd_5797456] using wordTrace_append hprefix tailTrace_5797456
  have hstable : (prefixWord ++ tailWord_5797456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797456).length < 2 ^ (prefixWord ++ tailWord_5797456).sum := by decide
  have hdescent : baseEnd_5797456 < baseStart_5797456 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797457 : List Nat := [1, 2, 2, 1, 3, 2, 4, 3, 1, 2, 2]
def baseStart_5797457 : Nat := 118140960795 + 5797457 * 2 ^ 59
def prefixEnd_5797457 : Nat := 4983230072969 + 3 ^ 40 * 5797457 * 2
def baseEnd_5797457 : Nat := 2976882014773029156525487

theorem tailTrace_5797457 : CollatzResearch.WordTrace tailWord_5797457 prefixEnd_5797457 2976882014773029156525487 := by
  unfold tailWord_5797457
  simp only [CollatzResearch.WordTrace]
  refine ⟨211450628157810890672686625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140967085438540593781791083 211450628157810890672686625)
  ·
    refine ⟨158587971118358168004514969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211450628157810890672686625 158587971118358168004514969)
    ·
      refine ⟨118940978338768626003386227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158587971118358168004514969 118940978338768626003386227)
      ·
        refine ⟨178411467508152939005079341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118940978338768626003386227 178411467508152939005079341)
        ·
          refine ⟨66904300315557352126904753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178411467508152939005079341 66904300315557352126904753)
          ·
            refine ⟨50178225236668014095178565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66904300315557352126904753 50178225236668014095178565)
            ·
              refine ⟨9408417231875252642845981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50178225236668014095178565 9408417231875252642845981)
              ·
                refine ⟨3528156461953219741067243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9408417231875252642845981 3528156461953219741067243)
                ·
                  refine ⟨5292234692929829611600865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3528156461953219741067243 5292234692929829611600865)
                  ·
                    refine ⟨3969176019697372208700649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5292234692929829611600865 3969176019697372208700649)
                    ·
                      refine ⟨2976882014773029156525487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3969176019697372208700649 2976882014773029156525487)
                      ·
                        rfl

theorem cell23_5797457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 3, 1, 2, 2].length) (baseStart_5797457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797457 prefixEnd_5797457 := by exact prefixLift 5797457
  have htrace : WordTrace (prefixWord ++ tailWord_5797457) baseStart_5797457 baseEnd_5797457 := by
    simpa [prefixWord, tailWord_5797457, baseEnd_5797457] using wordTrace_append hprefix tailTrace_5797457
  have hstable : (prefixWord ++ tailWord_5797457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797457).length < 2 ^ (prefixWord ++ tailWord_5797457).sum := by decide
  have hdescent : baseEnd_5797457 < baseStart_5797457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797473 : List Nat := [1, 2, 3, 1, 1, 3, 3, 1, 4, 1, 3]
def baseStart_5797473 : Nat := 118140960795 + 5797473 * 2 ^ 59
def prefixEnd_5797473 : Nat := 4983230072969 + 3 ^ 40 * 5797473 * 2
def baseEnd_5797473 : Nat := 2976890230463501093925413

theorem tailTrace_5797473 : CollatzResearch.WordTrace tailWord_5797473 prefixEnd_5797473 2976890230463501093925413 := by
  unfold tailWord_5797473
  simp only [CollatzResearch.WordTrace]
  refine ⟨211451211725752925405269073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140967474483835283603512715 211451211725752925405269073)
  ·
    refine ⟨158588408794314694053951805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211451211725752925405269073 158588408794314694053951805)
    ·
      refine ⟨59470653297868010270231927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158588408794314694053951805 59470653297868010270231927)
      ·
        refine ⟨89205979946802015405347891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59470653297868010270231927 89205979946802015405347891)
        ·
          refine ⟨133808969920203023108021837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89205979946802015405347891 133808969920203023108021837)
          ·
            refine ⟨50178363720076133665508189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133808969920203023108021837 50178363720076133665508189)
            ·
              refine ⟨18816886395028550124565571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50178363720076133665508189 18816886395028550124565571)
              ·
                refine ⟨28225329592542825186848357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18816886395028550124565571 28225329592542825186848357)
                ·
                  refine ⟨5292249298601779722534067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28225329592542825186848357 5292249298601779722534067)
                  ·
                    refine ⟨7938373947902669583801101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5292249298601779722534067 7938373947902669583801101)
                    ·
                      refine ⟨2976890230463501093925413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7938373947902669583801101 2976890230463501093925413)
                      ·
                        rfl

theorem cell23_5797473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 4, 1, 3].length) (baseStart_5797473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797473 prefixEnd_5797473 := by exact prefixLift 5797473
  have htrace : WordTrace (prefixWord ++ tailWord_5797473) baseStart_5797473 baseEnd_5797473 := by
    simpa [prefixWord, tailWord_5797473, baseEnd_5797473] using wordTrace_append hprefix tailTrace_5797473
  have hstable : (prefixWord ++ tailWord_5797473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797473).length < 2 ^ (prefixWord ++ tailWord_5797473).sum := by decide
  have hdescent : baseEnd_5797473 < baseStart_5797473 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797490 : List Nat := [3, 2, 1, 2, 3, 3, 1, 1, 1, 3, 3]
def baseStart_5797490 : Nat := 118140960795 + 5797490 * 2 ^ 59
def prefixEnd_5797490 : Nat := 4983230072969 + 3 ^ 40 * 5797490 * 2
def baseEnd_5797490 : Nat := 2976898959634627527412835

theorem tailTrace_5797490 : CollatzResearch.WordTrace tailWord_5797490 prefixEnd_5797490 2976898959634627527412835 := by
  unfold tailWord_5797490
  simp only [CollatzResearch.WordTrace]
  refine ⟨52862957941672834327159481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140967887844460891539091949 52862957941672834327159481)
  ·
    refine ⟨39647218456254625745369611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52862957941672834327159481 39647218456254625745369611)
    ·
      refine ⟨59470827684381938618054417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39647218456254625745369611 59470827684381938618054417)
      ·
        refine ⟨44603120763286453963540813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59470827684381938618054417 44603120763286453963540813)
        ·
          refine ⟨16726170286232420236327805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44603120763286453963540813 16726170286232420236327805)
          ·
            refine ⟨6272313857337157588622927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16726170286232420236327805 6272313857337157588622927)
            ·
              refine ⟨9408470786005736382934391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6272313857337157588622927 9408470786005736382934391)
              ·
                refine ⟨14112706179008604574401587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9408470786005736382934391 14112706179008604574401587)
                ·
                  refine ⟨21169059268512906861602381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14112706179008604574401587 21169059268512906861602381)
                  ·
                    refine ⟨7938397225692340073100893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21169059268512906861602381 7938397225692340073100893)
                    ·
                      refine ⟨2976898959634627527412835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7938397225692340073100893 2976898959634627527412835)
                      ·
                        rfl

theorem cell23_5797490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_5797490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797490 prefixEnd_5797490 := by exact prefixLift 5797490
  have htrace : WordTrace (prefixWord ++ tailWord_5797490) baseStart_5797490 baseEnd_5797490 := by
    simpa [prefixWord, tailWord_5797490, baseEnd_5797490] using wordTrace_append hprefix tailTrace_5797490
  have hstable : (prefixWord ++ tailWord_5797490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797490).length < 2 ^ (prefixWord ++ tailWord_5797490).sum := by decide
  have hdescent : baseEnd_5797490 < baseStart_5797490 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797513 : List Nat := [1, 2, 1, 1, 4, 1, 2, 4, 1, 4, 2]
def baseStart_5797513 : Nat := 118140960795 + 5797513 * 2 ^ 59
def prefixEnd_5797513 : Nat := 4983230072969 + 3 ^ 40 * 5797513 * 2
def baseEnd_5797513 : Nat := 2976910769689680937425229

theorem tailTrace_5797513 : CollatzResearch.WordTrace tailWord_5797513 prefixEnd_5797513 2976910769689680937425229 := by
  unfold tailWord_5797513
  simp only [CollatzResearch.WordTrace]
  refine ⟨211452670645608012236725193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140968447097072008157816795 211452670645608012236725193)
  ·
    refine ⟨158589502984206009177543895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211452670645608012236725193 158589502984206009177543895)
    ·
      refine ⟨237884254476309013766315843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158589502984206009177543895 237884254476309013766315843)
      ·
        refine ⟨356826381714463520649473765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237884254476309013766315843 356826381714463520649473765)
        ·
          refine ⟨66904946571461910121776331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 356826381714463520649473765 66904946571461910121776331)
          ·
            refine ⟨100357419857192865182664497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66904946571461910121776331 100357419857192865182664497)
            ·
              refine ⟨75268064892894648886998373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100357419857192865182664497 75268064892894648886998373)
              ·
                refine ⟨14112762167417746666312195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75268064892894648886998373 14112762167417746666312195)
                ·
                  refine ⟨21169143251126619999468293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14112762167417746666312195 21169143251126619999468293)
                  ·
                    refine ⟨3969214359586241249900305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21169143251126619999468293 3969214359586241249900305)
                    ·
                      refine ⟨2976910769689680937425229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3969214359586241249900305 2976910769689680937425229)
                      ·
                        rfl

theorem cell23_5797513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 4, 2].length) (baseStart_5797513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797513 prefixEnd_5797513 := by exact prefixLift 5797513
  have htrace : WordTrace (prefixWord ++ tailWord_5797513) baseStart_5797513 baseEnd_5797513 := by
    simpa [prefixWord, tailWord_5797513, baseEnd_5797513] using wordTrace_append hprefix tailTrace_5797513
  have hstable : (prefixWord ++ tailWord_5797513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797513).length < 2 ^ (prefixWord ++ tailWord_5797513).sum := by decide
  have hdescent : baseEnd_5797513 < baseStart_5797513 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797516 : List Nat := [2, 2, 1, 2, 1, 1, 5, 1, 2, 1, 5]
def baseStart_5797516 : Nat := 118140960795 + 5797516 * 2 ^ 59
def prefixEnd_5797516 : Nat := 4983230072969 + 3 ^ 40 * 5797516 * 2
def baseEnd_5797516 : Nat := 2976912310131644425687715

theorem tailTrace_5797516 : CollatzResearch.WordTrace tailWord_5797516 prefixEnd_5797516 2976912310131644425687715 := by
  unfold tailWord_5797516
  simp only [CollatzResearch.WordTrace]
  refine ⟨105726390032298571874542201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140968520043064762499389601 105726390032298571874542201)
  ·
    refine ⟨79294792524223928905906651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105726390032298571874542201 79294792524223928905906651)
    ·
      refine ⟨118942188786335893358859977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79294792524223928905906651 118942188786335893358859977)
      ·
        refine ⟨89206641589751920019144983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118942188786335893358859977 89206641589751920019144983)
        ·
          refine ⟨133809962384627880028717475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89206641589751920019144983 133809962384627880028717475)
          ·
            refine ⟨200714943576941820043076213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133809962384627880028717475 200714943576941820043076213)
            ·
              refine ⟨18817025960338295629038395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 200714943576941820043076213 18817025960338295629038395)
              ·
                refine ⟨28225538940507443443557593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18817025960338295629038395 28225538940507443443557593)
                ·
                  refine ⟨21169154205380582582668195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28225538940507443443557593 21169154205380582582668195)
                  ·
                    refine ⟨31753731308070873874002293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21169154205380582582668195 31753731308070873874002293)
                    ·
                      refine ⟨2976912310131644425687715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31753731308070873874002293 2976912310131644425687715)
                      ·
                        rfl

theorem cell23_5797516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_5797516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797516 prefixEnd_5797516 := by exact prefixLift 5797516
  have htrace : WordTrace (prefixWord ++ tailWord_5797516) baseStart_5797516 baseEnd_5797516 := by
    simpa [prefixWord, tailWord_5797516, baseEnd_5797516] using wordTrace_append hprefix tailTrace_5797516
  have hstable : (prefixWord ++ tailWord_5797516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797516).length < 2 ^ (prefixWord ++ tailWord_5797516).sum := by decide
  have hdescent : baseEnd_5797516 < baseStart_5797516 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797576 : List Nat := [2, 1, 3, 1, 2, 2, 1, 1, 3, 2, 5]
def baseStart_5797576 : Nat := 118140960795 + 5797576 * 2 ^ 59
def prefixEnd_5797576 : Nat := 4983230072969 + 3 ^ 40 * 5797576 * 2
def baseEnd_5797576 : Nat := 2976943118970914190937439

theorem tailTrace_5797576 : CollatzResearch.WordTrace tailWord_5797576 prefixEnd_5797576 2976943118970914190937439 := by
  unfold tailWord_5797576
  simp only [CollatzResearch.WordTrace]
  refine ⟨105727484222189886998134291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140969978962919849330845721 105727484222189886998134291)
  ·
    refine ⟨158591226333284830497201437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105727484222189886998134291 158591226333284830497201437)
    ·
      refine ⟨59471709874981811436450539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158591226333284830497201437 59471709874981811436450539)
      ·
        refine ⟨89207564812472717154675809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59471709874981811436450539 89207564812472717154675809)
        ·
          refine ⟨66905673609354537866006857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89207564812472717154675809 66905673609354537866006857)
          ·
            refine ⟨50179255207015903399505143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66905673609354537866006857 50179255207015903399505143)
            ·
              refine ⟨75268882810523855099257715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50179255207015903399505143 75268882810523855099257715)
              ·
                refine ⟨112903324215785782648886573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75268882810523855099257715 112903324215785782648886573)
                ·
                  refine ⟨42338746580919668493332465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112903324215785782648886573 42338746580919668493332465)
                  ·
                    refine ⟨31754059935689751369999349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42338746580919668493332465 31754059935689751369999349)
                    ·
                      refine ⟨2976943118970914190937439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31754059935689751369999349 2976943118970914190937439)
                      ·
                        rfl

theorem cell23_5797576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_5797576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797576 prefixEnd_5797576 := by exact prefixLift 5797576
  have htrace : WordTrace (prefixWord ++ tailWord_5797576) baseStart_5797576 baseEnd_5797576 := by
    simpa [prefixWord, tailWord_5797576, baseEnd_5797576] using wordTrace_append hprefix tailTrace_5797576
  have hstable : (prefixWord ++ tailWord_5797576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797576).length < 2 ^ (prefixWord ++ tailWord_5797576).sum := by decide
  have hdescent : baseEnd_5797576 < baseStart_5797576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797581 : List Nat := [1, 6, 2, 1, 1, 2, 2, 2, 2, 2, 2]
def baseStart_5797581 : Nat := 118140960795 + 5797581 * 2 ^ 59
def prefixEnd_5797581 : Nat := 4983230072969 + 3 ^ 40 * 5797581 * 2
def baseEnd_5797581 : Nat := 2976945686374186671374917

theorem tailTrace_5797581 : CollatzResearch.WordTrace tailWord_5797581 prefixEnd_5797581 2976945686374186671374917 := by
  unfold tailWord_5797581
  simp only [CollatzResearch.WordTrace]
  refine ⟨211455150809361659850200597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140970100539574439900133731 211455150809361659850200597)
  ·
    refine ⟨9911960194188827805478153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 211455150809361659850200597 9911960194188827805478153)
    ·
      refine ⟨7433970145641620854108615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9911960194188827805478153 7433970145641620854108615)
      ·
        refine ⟨11150955218462431281162923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7433970145641620854108615 11150955218462431281162923)
        ·
          refine ⟨16726432827693646921744385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11150955218462431281162923 16726432827693646921744385)
          ·
            refine ⟨12544824620770235191308289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16726432827693646921744385 12544824620770235191308289)
            ·
              refine ⟨9408618465577676393481217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12544824620770235191308289 9408618465577676393481217)
              ·
                refine ⟨7056463849183257295110913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9408618465577676393481217 7056463849183257295110913)
                ·
                  refine ⟨5292347886887442971333185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7056463849183257295110913 5292347886887442971333185)
                  ·
                    refine ⟨3969260915165582228499889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5292347886887442971333185 3969260915165582228499889)
                    ·
                      refine ⟨2976945686374186671374917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3969260915165582228499889 2976945686374186671374917)
                      ·
                        rfl

theorem cell23_5797581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_5797581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797581 prefixEnd_5797581 := by exact prefixLift 5797581
  have htrace : WordTrace (prefixWord ++ tailWord_5797581) baseStart_5797581 baseEnd_5797581 := by
    simpa [prefixWord, tailWord_5797581, baseEnd_5797581] using wordTrace_append hprefix tailTrace_5797581
  have hstable : (prefixWord ++ tailWord_5797581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797581).length < 2 ^ (prefixWord ++ tailWord_5797581).sum := by decide
  have hdescent : baseEnd_5797581 < baseStart_5797581 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797597 : List Nat := [1, 4, 3, 3, 1, 1, 1, 1, 2, 3, 3]
def baseStart_5797597 : Nat := 118140960795 + 5797597 * 2 ^ 59
def prefixEnd_5797597 : Nat := 4983230072969 + 3 ^ 40 * 5797597 * 2
def baseEnd_5797597 : Nat := 2976953902064658608774843

theorem tailTrace_5797597 : CollatzResearch.WordTrace tailWord_5797597 prefixEnd_5797597 2976953902064658608774843 := by
  unfold tailWord_5797597
  simp only [CollatzResearch.WordTrace]
  refine ⟨211455734377303694582783045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140970489584869129721855363 211455734377303694582783045)
  ·
    refine ⟨39647950195744442734271821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 211455734377303694582783045 39647950195744442734271821)
    ·
      refine ⟨14867981323404166025351933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39647950195744442734271821 14867981323404166025351933)
      ·
        refine ⟨5575492996276562259506975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14867981323404166025351933 5575492996276562259506975)
        ·
          refine ⟨8363239494414843389260463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5575492996276562259506975 8363239494414843389260463)
          ·
            refine ⟨12544859241622265083890695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8363239494414843389260463 12544859241622265083890695)
            ·
              refine ⟨18817288862433397625836043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12544859241622265083890695 18817288862433397625836043)
              ·
                refine ⟨28225933293650096438754065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18817288862433397625836043 28225933293650096438754065)
                ·
                  refine ⟨21169449970237572329065549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28225933293650096438754065 21169449970237572329065549)
                  ·
                    refine ⟨7938543738839089623399581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21169449970237572329065549 7938543738839089623399581)
                    ·
                      refine ⟨2976953902064658608774843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7938543738839089623399581 2976953902064658608774843)
                      ·
                        rfl

theorem cell23_5797597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_5797597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797597 prefixEnd_5797597 := by exact prefixLift 5797597
  have htrace : WordTrace (prefixWord ++ tailWord_5797597) baseStart_5797597 baseEnd_5797597 := by
    simpa [prefixWord, tailWord_5797597, baseEnd_5797597] using wordTrace_append hprefix tailTrace_5797597
  have hstable : (prefixWord ++ tailWord_5797597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797597).length < 2 ^ (prefixWord ++ tailWord_5797597).sum := by decide
  have hdescent : baseEnd_5797597 < baseStart_5797597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797616 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 4]
def baseStart_5797616 : Nat := 118140960795 + 5797616 * 2 ^ 59
def prefixEnd_5797616 : Nat := 4983230072969 + 3 ^ 40 * 5797616 * 2
def baseEnd_5797616 : Nat := 2976963658197094034437255

theorem tailTrace_5797616 : CollatzResearch.WordTrace tailWord_5797616 prefixEnd_5797616 2976963658197094034437255 := by
  unfold tailWord_5797616
  simp only [CollatzResearch.WordTrace]
  refine ⟨105728213682117430413862351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140970951576156573885149801 105728213682117430413862351)
  ·
    refine ⟨158592320523176145620793527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105728213682117430413862351 158592320523176145620793527)
    ·
      refine ⟨237888480784764218431190291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158592320523176145620793527 237888480784764218431190291)
      ·
        refine ⟨356832721177146327646785437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237888480784764218431190291 356832721177146327646785437)
        ·
          refine ⟨133812270441429872867544539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 356832721177146327646785437 133812270441429872867544539)
          ·
            refine ⟨200718405662144809301316809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133812270441429872867544539 200718405662144809301316809)
            ·
              refine ⟨150538804246608606975987607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200718405662144809301316809 150538804246608606975987607)
              ·
                refine ⟨225808206369912910463981411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150538804246608606975987607 225808206369912910463981411)
                ·
                  refine ⟨338712309554869365695972117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 225808206369912910463981411 338712309554869365695972117)
                  ·
                    refine ⟨15877139510384501516998693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 338712309554869365695972117 15877139510384501516998693)
                    ·
                      refine ⟨2976963658197094034437255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15877139510384501516998693 2976963658197094034437255)
                      ·
                        rfl

theorem cell23_5797616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 4].length) (baseStart_5797616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797616 prefixEnd_5797616 := by exact prefixLift 5797616
  have htrace : WordTrace (prefixWord ++ tailWord_5797616) baseStart_5797616 baseEnd_5797616 := by
    simpa [prefixWord, tailWord_5797616, baseEnd_5797616] using wordTrace_append hprefix tailTrace_5797616
  have hstable : (prefixWord ++ tailWord_5797616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797616).length < 2 ^ (prefixWord ++ tailWord_5797616).sum := by decide
  have hdescent : baseEnd_5797616 < baseStart_5797616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797626 : List Nat := [3, 1, 1, 1, 1, 3, 1, 4, 8]
def baseStart_5797626 : Nat := 118140960795 + 5797626 * 2 ^ 59
def prefixEnd_5797626 : Nat := 4983230072969 + 3 ^ 40 * 5797626 * 2
def baseEnd_5797626 : Nat := 330774310333737666145801

theorem tailTrace_5797626 : CollatzResearch.WordTrace tailWord_5797626 prefixEnd_5797626 330774310333737666145801 := by
  unfold tailWord_5797626
  simp only [CollatzResearch.WordTrace]
  refine ⟨52864198023549658133897183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140971194729465755023725821 52864198023549658133897183)
  ·
    refine ⟨79296297035324487200845775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52864198023549658133897183 79296297035324487200845775)
    ·
      refine ⟨118944445552986730801268663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79296297035324487200845775 118944445552986730801268663)
      ·
        refine ⟨178416668329480096201902995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118944445552986730801268663 178416668329480096201902995)
        ·
          refine ⟨267625002494220144302854493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178416668329480096201902995 267625002494220144302854493)
          ·
            refine ⟨100359375935332554113570435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 267625002494220144302854493 100359375935332554113570435)
            ·
              refine ⟨150539063902998831170355653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100359375935332554113570435 150539063902998831170355653)
              ·
                refine ⟨28226074481812280844441685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 150539063902998831170355653 28226074481812280844441685)
                ·
                  refine ⟨330774310333737666145801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28226074481812280844441685 330774310333737666145801)
                  ·
                    rfl

theorem cell23_5797626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 8].length) (baseStart_5797626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797626 prefixEnd_5797626 := by exact prefixLift 5797626
  have htrace : WordTrace (prefixWord ++ tailWord_5797626) baseStart_5797626 baseEnd_5797626 := by
    simpa [prefixWord, tailWord_5797626, baseEnd_5797626] using wordTrace_append hprefix tailTrace_5797626
  have hstable : (prefixWord ++ tailWord_5797626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797626).length < 2 ^ (prefixWord ++ tailWord_5797626).sum := by decide
  have hdescent : baseEnd_5797626 < baseStart_5797626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797643 : List Nat := [1, 1, 1, 1, 5, 1, 5, 2, 6]
def baseStart_5797643 : Nat := 118140960795 + 5797643 * 2 ^ 59
def prefixEnd_5797643 : Nat := 4983230072969 + 3 ^ 40 * 5797643 * 2
def baseEnd_5797643 : Nat := 330775280241640603199959

theorem tailTrace_5797643 : CollatzResearch.WordTrace tailWord_5797643 prefixEnd_5797643 330775280241640603199959 := by
  unfold tailWord_5797643
  simp only [CollatzResearch.WordTrace]
  refine ⟨211457412135137044438957583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140971608090091362959305055 211457412135137044438957583)
  ·
    refine ⟨317186118202705566658436375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211457412135137044438957583 317186118202705566658436375)
    ·
      refine ⟨475779177304058349987654563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317186118202705566658436375 475779177304058349987654563)
      ·
        refine ⟨713668765956087524981481845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475779177304058349987654563 713668765956087524981481845)
        ·
          refine ⟨66906446808383205467013923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 713668765956087524981481845 66906446808383205467013923)
          ·
            refine ⟨100359670212574808200520885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66906446808383205467013923 100359670212574808200520885)
            ·
              refine ⟨9408719082428888268798833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 100359670212574808200520885 9408719082428888268798833)
              ·
                refine ⟨7056539311821666201599125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9408719082428888268798833 7056539311821666201599125)
                ·
                  refine ⟨330775280241640603199959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7056539311821666201599125 330775280241640603199959)
                  ·
                    rfl

theorem cell23_5797643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 2, 6].length) (baseStart_5797643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797643 prefixEnd_5797643 := by exact prefixLift 5797643
  have htrace : WordTrace (prefixWord ++ tailWord_5797643) baseStart_5797643 baseEnd_5797643 := by
    simpa [prefixWord, tailWord_5797643, baseEnd_5797643] using wordTrace_append hprefix tailTrace_5797643
  have hstable : (prefixWord ++ tailWord_5797643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797643).length < 2 ^ (prefixWord ++ tailWord_5797643).sum := by decide
  have hdescent : baseEnd_5797643 < baseStart_5797643 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797660 : List Nat := [2, 2, 3, 1, 1, 2, 5, 1, 6]
def baseStart_5797660 : Nat := 118140960795 + 5797660 * 2 ^ 59
def prefixEnd_5797660 : Nat := 4983230072969 + 3 ^ 40 * 5797660 * 2
def baseEnd_5797660 : Nat := 330776250149543540254117

theorem tailTrace_5797660 : CollatzResearch.WordTrace tailWord_5797660 prefixEnd_5797660 330776250149543540254117 := by
  unfold tailWord_5797660
  simp only [CollatzResearch.WordTrace]
  refine ⟨105729016088037728171163217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140972021450716970894884289 105729016088037728171163217)
  ·
    refine ⟨79296762066028296128372413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105729016088037728171163217 79296762066028296128372413)
    ·
      refine ⟨29736285774760611048139655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79296762066028296128372413 29736285774760611048139655)
      ·
        refine ⟨44604428662140916572209483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29736285774760611048139655 44604428662140916572209483)
        ·
          refine ⟨66906642993211374858314225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44604428662140916572209483 66906642993211374858314225)
          ·
            refine ⟨50179982244908531143735669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66906642993211374858314225 50179982244908531143735669)
            ·
              refine ⟨4704373335460174794725219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50179982244908531143735669 4704373335460174794725219)
              ·
                refine ⟨7056560003190262192087829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4704373335460174794725219 7056560003190262192087829)
                ·
                  refine ⟨330776250149543540254117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7056560003190262192087829 330776250149543540254117)
                  ·
                    rfl

theorem cell23_5797660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 1, 6].length) (baseStart_5797660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797660 prefixEnd_5797660 := by exact prefixLift 5797660
  have htrace : WordTrace (prefixWord ++ tailWord_5797660) baseStart_5797660 baseEnd_5797660 := by
    simpa [prefixWord, tailWord_5797660, baseEnd_5797660] using wordTrace_append hprefix tailTrace_5797660
  have hstable : (prefixWord ++ tailWord_5797660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797660).length < 2 ^ (prefixWord ++ tailWord_5797660).sum := by decide
  have hdescent : baseEnd_5797660 < baseStart_5797660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797687 : List Nat := [1, 1, 3, 1, 2, 1, 2, 7, 1, 1, 3]
def baseStart_5797687 : Nat := 118140960795 + 5797687 * 2 ^ 59
def prefixEnd_5797687 : Nat := 4983230072969 + 3 ^ 40 * 5797687 * 2
def baseEnd_5797687 : Nat := 2977000115323563256649429

theorem tailTrace_5797687 : CollatzResearch.WordTrace tailWord_5797687 prefixEnd_5797687 2977000115323563256649429 := by
  unfold tailWord_5797687
  simp only [CollatzResearch.WordTrace]
  refine ⟨211459016946977639953559315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140972677964651759969039543 211459016946977639953559315)
  ·
    refine ⟨317188525420466459930338973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211459016946977639953559315 317188525420466459930338973)
    ·
      refine ⟨118945697032674922473877115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 317188525420466459930338973 118945697032674922473877115)
      ·
        refine ⟨178418545549012383710815673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118945697032674922473877115 178418545549012383710815673)
        ·
          refine ⟨133813909161759287783111755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178418545549012383710815673 133813909161759287783111755)
          ·
            refine ⟨200720863742638931674667633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133813909161759287783111755 200720863742638931674667633)
            ·
              refine ⟨150540647806979198756000725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200720863742638931674667633 150540647806979198756000725)
              ·
                refine ⟨3528296432976074970843767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 150540647806979198756000725 3528296432976074970843767)
                ·
                  refine ⟨5292444649464112456265651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3528296432976074970843767 5292444649464112456265651)
                  ·
                    refine ⟨7938666974196168684398477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5292444649464112456265651 7938666974196168684398477)
                    ·
                      refine ⟨2977000115323563256649429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7938666974196168684398477 2977000115323563256649429)
                      ·
                        rfl

theorem cell23_5797687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 7, 1, 1, 3].length) (baseStart_5797687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797687 prefixEnd_5797687 := by exact prefixLift 5797687
  have htrace : WordTrace (prefixWord ++ tailWord_5797687) baseStart_5797687 baseEnd_5797687 := by
    simpa [prefixWord, tailWord_5797687, baseEnd_5797687] using wordTrace_append hprefix tailTrace_5797687
  have hstable : (prefixWord ++ tailWord_5797687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797687).length < 2 ^ (prefixWord ++ tailWord_5797687).sum := by decide
  have hdescent : baseEnd_5797687 < baseStart_5797687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797690 : List Nat := [3, 1, 1, 1, 5, 1, 2, 3, 1, 5]
def baseStart_5797690 : Nat := 118140960795 + 5797690 * 2 ^ 59
def prefixEnd_5797690 : Nat := 4983230072969 + 3 ^ 40 * 5797690 * 2
def baseEnd_5797690 : Nat := 992333885255175581637305

theorem tailTrace_5797690 : CollatzResearch.WordTrace tailWord_5797690 prefixEnd_5797690 992333885255175581637305 := by
  unfold tailWord_5797690
  simp only [CollatzResearch.WordTrace]
  refine ⟨52864781591491692866479631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140972750910644514310612349 52864781591491692866479631)
  ·
    refine ⟨79297172387237539299719447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52864781591491692866479631 79297172387237539299719447)
    ·
      refine ⟨118945758580856308949579171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79297172387237539299719447 118945758580856308949579171)
      ·
        refine ⟨178418637871284463424368757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118945758580856308949579171 178418637871284463424368757)
        ·
          refine ⟨16726747300432918446034571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 178418637871284463424368757 16726747300432918446034571)
          ·
            refine ⟨25090120950649377669051857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16726747300432918446034571 25090120950649377669051857)
            ·
              refine ⟨18817590712987033251788893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25090120950649377669051857 18817590712987033251788893)
              ·
                refine ⟨7056596517370137469420835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18817590712987033251788893 7056596517370137469420835)
                ·
                  refine ⟨10584894776055206204131253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7056596517370137469420835 10584894776055206204131253)
                  ·
                    refine ⟨992333885255175581637305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10584894776055206204131253 992333885255175581637305)
                    ·
                      rfl

theorem cell23_5797690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 3, 1, 5].length) (baseStart_5797690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797690 prefixEnd_5797690 := by exact prefixLift 5797690
  have htrace : WordTrace (prefixWord ++ tailWord_5797690) baseStart_5797690 baseEnd_5797690 := by
    simpa [prefixWord, tailWord_5797690, baseEnd_5797690] using wordTrace_append hprefix tailTrace_5797690
  have hstable : (prefixWord ++ tailWord_5797690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797690).length < 2 ^ (prefixWord ++ tailWord_5797690).sum := by decide
  have hdescent : baseEnd_5797690 < baseStart_5797690 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797724 : List Nat := [2, 2, 4, 2, 2, 2, 1, 2, 1, 5]
def baseStart_5797724 : Nat := 118140960795 + 5797724 * 2 ^ 59
def prefixEnd_5797724 : Nat := 4983230072969 + 3 ^ 40 * 5797724 * 2
def baseEnd_5797724 : Nat := 992339704702593203962253

theorem tailTrace_5797724 : CollatzResearch.WordTrace tailWord_5797724 prefixEnd_5797724 992339704702593203962253 := by
  unfold tailWord_5797724
  simp only [CollatzResearch.WordTrace]
  refine ⟨105730183223921797636328113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140973577631895730181770817 105730183223921797636328113)
  ·
    refine ⟨79297637417941348227246085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105730183223921797636328113 79297637417941348227246085)
    ·
      refine ⟨14868307015864002792608641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79297637417941348227246085 14868307015864002792608641)
      ·
        refine ⟨11151230261898002094456481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14868307015864002792608641 11151230261898002094456481)
        ·
          refine ⟨8363422696423501570842361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11151230261898002094456481 8363422696423501570842361)
          ·
            refine ⟨6272567022317626178131771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8363422696423501570842361 6272567022317626178131771)
            ·
              refine ⟨9408850533476439267197657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6272567022317626178131771 9408850533476439267197657)
              ·
                refine ⟨7056637900107329450398243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9408850533476439267197657 7056637900107329450398243)
                ·
                  refine ⟨10584956850160994175597365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7056637900107329450398243 10584956850160994175597365)
                  ·
                    refine ⟨992339704702593203962253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10584956850160994175597365 992339704702593203962253)
                    ·
                      rfl

theorem cell23_5797724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_5797724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797724 prefixEnd_5797724 := by exact prefixLift 5797724
  have htrace : WordTrace (prefixWord ++ tailWord_5797724) baseStart_5797724 baseEnd_5797724 := by
    simpa [prefixWord, tailWord_5797724, baseEnd_5797724] using wordTrace_append hprefix tailTrace_5797724
  have hstable : (prefixWord ++ tailWord_5797724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797724).length < 2 ^ (prefixWord ++ tailWord_5797724).sum := by decide
  have hdescent : baseEnd_5797724 < baseStart_5797724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797727 : List Nat := [1, 1, 2, 3, 1, 6, 1, 2, 1, 1, 4]
def baseStart_5797727 : Nat := 118140960795 + 5797727 * 2 ^ 59
def prefixEnd_5797727 : Nat := 4983230072969 + 3 ^ 40 * 5797727 * 2
def baseEnd_5797727 : Nat := 2977020654549743100149245

theorem tailTrace_5797727 : CollatzResearch.WordTrace tailWord_5797727 prefixEnd_5797727 2977020654549743100149245 := by
  unfold tailWord_5797727
  simp only [CollatzResearch.WordTrace]
  refine ⟨211460475866832726785015435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140973650577888484523343623 211460475866832726785015435)
  ·
    refine ⟨317190713800249090177523153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211460475866832726785015435 317190713800249090177523153)
    ·
      refine ⟨237893035350186817633142365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317190713800249090177523153 237893035350186817633142365)
      ·
        refine ⟨89209888256320056612428387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 237893035350186817633142365 89209888256320056612428387)
        ·
          refine ⟨133814832384480084918642581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89209888256320056612428387 133814832384480084918642581)
          ·
            refine ⟨6272570268022503980561371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 133814832384480084918642581 6272570268022503980561371)
            ·
              refine ⟨9408855402033755970842057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6272570268022503980561371 9408855402033755970842057)
              ·
                refine ⟨7056641551525316978131543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9408855402033755970842057 7056641551525316978131543)
                ·
                  refine ⟨10584962327287975467197315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7056641551525316978131543 10584962327287975467197315)
                  ·
                    refine ⟨15877443490931963200795973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10584962327287975467197315 15877443490931963200795973)
                    ·
                      refine ⟨2977020654549743100149245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15877443490931963200795973 2977020654549743100149245)
                      ·
                        rfl

theorem cell23_5797727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 2, 1, 1, 4].length) (baseStart_5797727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797727 prefixEnd_5797727 := by exact prefixLift 5797727
  have htrace : WordTrace (prefixWord ++ tailWord_5797727) baseStart_5797727 baseEnd_5797727 := by
    simpa [prefixWord, tailWord_5797727, baseEnd_5797727] using wordTrace_append hprefix tailTrace_5797727
  have hstable : (prefixWord ++ tailWord_5797727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797727).length < 2 ^ (prefixWord ++ tailWord_5797727).sum := by decide
  have hdescent : baseEnd_5797727 < baseStart_5797727 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797740 : List Nat := [2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 4]
def baseStart_5797740 : Nat := 118140960795 + 5797740 * 2 ^ 59
def prefixEnd_5797740 : Nat := 4983230072969 + 3 ^ 40 * 5797740 * 2
def baseEnd_5797740 : Nat := 2977027329798251549286685

theorem tailTrace_5797740 : CollatzResearch.WordTrace tailWord_5797740 prefixEnd_5797740 2977027329798251549286685 := by
  unfold tailWord_5797740
  simp only [CollatzResearch.WordTrace]
  refine ⟨105730475007892815002619337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140973966677190420003492449 105730475007892815002619337)
  ·
    refine ⟨79297856255919611251964503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105730475007892815002619337 79297856255919611251964503)
    ·
      refine ⟨118946784383879416877946755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79297856255919611251964503 118946784383879416877946755)
      ·
        refine ⟨178420176575819125316920133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118946784383879416877946755 178420176575819125316920133)
        ·
          refine ⟨33453783107966085996922525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 178420176575819125316920133 33453783107966085996922525)
          ·
            refine ⟨12545168665487282248845947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33453783107966085996922525 12545168665487282248845947)
            ·
              refine ⟨18817752998230923373268921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12545168665487282248845947 18817752998230923373268921)
              ·
                refine ⟨14113314748673192529951691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18817752998230923373268921 14113314748673192529951691)
                ·
                  refine ⟨21169972123009788794927537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14113314748673192529951691 21169972123009788794927537)
                  ·
                    refine ⟨15877479092257341596195653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21169972123009788794927537 15877479092257341596195653)
                    ·
                      refine ⟨2977027329798251549286685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15877479092257341596195653 2977027329798251549286685)
                      ·
                        rfl

theorem cell23_5797740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 4].length) (baseStart_5797740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797740 prefixEnd_5797740 := by exact prefixLift 5797740
  have htrace : WordTrace (prefixWord ++ tailWord_5797740) baseStart_5797740 baseEnd_5797740 := by
    simpa [prefixWord, tailWord_5797740, baseEnd_5797740] using wordTrace_append hprefix tailTrace_5797740
  have hstable : (prefixWord ++ tailWord_5797740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797740).length < 2 ^ (prefixWord ++ tailWord_5797740).sum := by decide
  have hdescent : baseEnd_5797740 < baseStart_5797740 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797744 : List Nat := [2, 1, 1, 1, 4, 1, 1, 7, 1, 2, 2]
def baseStart_5797744 : Nat := 118140960795 + 5797744 * 2 ^ 59
def prefixEnd_5797744 : Nat := 4983230072969 + 3 ^ 40 * 5797744 * 2
def baseEnd_5797744 : Nat := 2977029383720869533636667

theorem tailTrace_5797744 : CollatzResearch.WordTrace tailWord_5797744 prefixEnd_5797744 2977029383720869533636667 := by
  unfold tailWord_5797744
  simp only [CollatzResearch.WordTrace]
  refine ⟨105730547953885569344192143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140974063938514092458922857 105730547953885569344192143)
  ·
    refine ⟨158595821930828354016288215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105730547953885569344192143 158595821930828354016288215)
    ·
      refine ⟨237893732896242531024432323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158595821930828354016288215 237893732896242531024432323)
      ·
        refine ⟨356840599344363796536648485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237893732896242531024432323 356840599344363796536648485)
        ·
          refine ⟨66907612377068211850621591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 356840599344363796536648485 66907612377068211850621591)
          ·
            refine ⟨100361418565602317775932387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66907612377068211850621591 100361418565602317775932387)
            ·
              refine ⟨150542127848403476663898581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100361418565602317775932387 150542127848403476663898581)
              ·
                refine ⟨3528331121446956484310123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 150542127848403476663898581 3528331121446956484310123)
                ·
                  refine ⟨5292496682170434726465185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3528331121446956484310123 5292496682170434726465185)
                  ·
                    refine ⟨3969372511627826044848889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5292496682170434726465185 3969372511627826044848889)
                    ·
                      refine ⟨2977029383720869533636667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3969372511627826044848889 2977029383720869533636667)
                      ·
                        rfl

theorem cell23_5797744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 7, 1, 2, 2].length) (baseStart_5797744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797744 prefixEnd_5797744 := by exact prefixLift 5797744
  have htrace : WordTrace (prefixWord ++ tailWord_5797744) baseStart_5797744 baseEnd_5797744 := by
    simpa [prefixWord, tailWord_5797744, baseEnd_5797744] using wordTrace_append hprefix tailTrace_5797744
  have hstable : (prefixWord ++ tailWord_5797744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797744).length < 2 ^ (prefixWord ++ tailWord_5797744).sum := by decide
  have hdescent : baseEnd_5797744 < baseStart_5797744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797750 : List Nat := [5, 1, 1, 3, 2, 11]
def baseStart_5797750 : Nat := 118140960795 + 5797750 * 2 ^ 59
def prefixEnd_5797750 : Nat := 4983230072969 + 3 ^ 40 * 5797750 * 2
def baseEnd_5797750 : Nat := 12251162405781055597373

theorem tailTrace_5797750 : CollatzResearch.WordTrace tailWord_5797750 prefixEnd_5797750 12251162405781055597373 := by
  unfold tailWord_5797750
  simp only [CollatzResearch.WordTrace]
  refine ⟨13216332171609337607068919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 140974209830499601142068469 13216332171609337607068919)
  ·
    refine ⟨19824498257414006410603379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13216332171609337607068919 19824498257414006410603379)
    ·
      refine ⟨29736747386121009615905069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19824498257414006410603379 29736747386121009615905069)
      ·
        refine ⟨11151280269795378605964401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29736747386121009615905069 11151280269795378605964401)
        ·
          refine ⟨8363460202346533954473301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11151280269795378605964401 8363460202346533954473301)
          ·
            refine ⟨12251162405781055597373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8363460202346533954473301 12251162405781055597373)
            ·
              rfl

theorem cell23_5797750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 11].length) (baseStart_5797750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797750 prefixEnd_5797750 := by exact prefixLift 5797750
  have htrace : WordTrace (prefixWord ++ tailWord_5797750) baseStart_5797750 baseEnd_5797750 := by
    simpa [prefixWord, tailWord_5797750, baseEnd_5797750] using wordTrace_append hprefix tailTrace_5797750
  have hstable : (prefixWord ++ tailWord_5797750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797750).length < 2 ^ (prefixWord ++ tailWord_5797750).sum := by decide
  have hdescent : baseEnd_5797750 < baseStart_5797750 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797763 : List Nat := [1, 1, 1, 3, 4, 2, 1, 1, 2, 7]
def baseStart_5797763 : Nat := 118140960795 + 5797763 * 2 ^ 59
def prefixEnd_5797763 : Nat := 4983230072969 + 3 ^ 40 * 5797763 * 2
def baseEnd_5797763 : Nat := 992346379951101653099693

theorem tailTrace_5797763 : CollatzResearch.WordTrace tailWord_5797763 prefixEnd_5797763 992346379951101653099693 := by
  unfold tailWord_5797763
  simp only [CollatzResearch.WordTrace]
  refine ⟨211461788894702304933325943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140974525929801536622217295 211461788894702304933325943)
  ·
    refine ⟨317192683342053457399988915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211461788894702304933325943 317192683342053457399988915)
    ·
      refine ⟨475789025013080186099983373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317192683342053457399988915 475789025013080186099983373)
      ·
        refine ⟨178420884379905069787493765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 475789025013080186099983373 178420884379905069787493765)
        ·
          refine ⟨33453915821232200585155081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 178420884379905069787493765 33453915821232200585155081)
          ·
            refine ⟨25090436865924150438866311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33453915821232200585155081 25090436865924150438866311)
            ·
              refine ⟨37635655298886225658299467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25090436865924150438866311 37635655298886225658299467)
              ·
                refine ⟨56453482948329338487449201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37635655298886225658299467 56453482948329338487449201)
                ·
                  refine ⟨42340112211247003865586901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56453482948329338487449201 42340112211247003865586901)
                  ·
                    refine ⟨992346379951101653099693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42340112211247003865586901 992346379951101653099693)
                    ·
                      rfl

theorem cell23_5797763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 7].length) (baseStart_5797763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797763 prefixEnd_5797763 := by exact prefixLift 5797763
  have htrace : WordTrace (prefixWord ++ tailWord_5797763) baseStart_5797763 baseEnd_5797763 := by
    simpa [prefixWord, tailWord_5797763, baseEnd_5797763] using wordTrace_append hprefix tailTrace_5797763
  have hstable : (prefixWord ++ tailWord_5797763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797763).length < 2 ^ (prefixWord ++ tailWord_5797763).sum := by decide
  have hdescent : baseEnd_5797763 < baseStart_5797763 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797767 : List Nat := [1, 1, 4, 2, 5, 1, 1, 8]
def baseStart_5797767 : Nat := 118140960795 + 5797767 * 2 ^ 59
def prefixEnd_5797767 : Nat := 4983230072969 + 3 ^ 40 * 5797767 * 2
def baseEnd_5797767 : Nat := 110260784954663812727743

theorem tailTrace_5797767 : CollatzResearch.WordTrace tailWord_5797767 prefixEnd_5797767 110260784954663812727743 := by
  unfold tailWord_5797767
  simp only [CollatzResearch.WordTrace]
  refine ⟨211461934786687813616471555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140974623191125209077647703 211461934786687813616471555)
  ·
    refine ⟨317192902180031720424707333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211461934786687813616471555 317192902180031720424707333)
    ·
      refine ⟨59473669158755947579632625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 317192902180031720424707333 59473669158755947579632625)
      ·
        refine ⟨44605251869066960684724469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59473669158755947579632625 44605251869066960684724469)
        ·
          refine ⟨4181742362725027564192919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44605251869066960684724469 4181742362725027564192919)
          ·
            refine ⟨6272613544087541346289379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4181742362725027564192919 6272613544087541346289379)
            ·
              refine ⟨9408920316131312019434069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6272613544087541346289379 9408920316131312019434069)
              ·
                refine ⟨110260784954663812727743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9408920316131312019434069 110260784954663812727743)
                ·
                  rfl

theorem cell23_5797767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 8].length) (baseStart_5797767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797767 prefixEnd_5797767 := by exact prefixLift 5797767
  have htrace : WordTrace (prefixWord ++ tailWord_5797767) baseStart_5797767 baseEnd_5797767 := by
    simpa [prefixWord, tailWord_5797767, baseEnd_5797767] using wordTrace_append hprefix tailTrace_5797767
  have hstable : (prefixWord ++ tailWord_5797767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797767).length < 2 ^ (prefixWord ++ tailWord_5797767).sum := by decide
  have hdescent : baseEnd_5797767 < baseStart_5797767 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797774 : List Nat := [4, 1, 1, 5, 1, 1, 2, 1, 1, 2, 4]
def baseStart_5797774 : Nat := 118140960795 + 5797774 * 2 ^ 59
def prefixEnd_5797774 : Nat := 4983230072969 + 3 ^ 40 * 5797774 * 2
def baseEnd_5797774 : Nat := 2977044788140504416261529

theorem tailTrace_5797774 : CollatzResearch.WordTrace tailWord_5797774 prefixEnd_5797774 2977044788140504416261529 := by
  unfold tailWord_5797774
  simp only [CollatzResearch.WordTrace]
  refine ⟨26432773762207806726497047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140974793398441635874650917 26432773762207806726497047)
  ·
    refine ⟨39649160643311710089745571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26432773762207806726497047 39649160643311710089745571)
    ·
      refine ⟨59473740964967565134618357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39649160643311710089745571 59473740964967565134618357)
      ·
        refine ⟨5575663215465709231370471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59473740964967565134618357 5575663215465709231370471)
        ·
          refine ⟨8363494823198563847055707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5575663215465709231370471 8363494823198563847055707)
          ·
            refine ⟨12545242234797845770583561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8363494823198563847055707 12545242234797845770583561)
            ·
              refine ⟨9408931676098384327937671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12545242234797845770583561 9408931676098384327937671)
              ·
                refine ⟨14113397514147576491906507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9408931676098384327937671 14113397514147576491906507)
                ·
                  refine ⟨21170096271221364737859761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14113397514147576491906507 21170096271221364737859761)
                  ·
                    refine ⟨15877572203416023553394821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21170096271221364737859761 15877572203416023553394821)
                    ·
                      refine ⟨2977044788140504416261529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15877572203416023553394821 2977044788140504416261529)
                      ·
                        rfl

theorem cell23_5797774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_5797774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797774 prefixEnd_5797774 := by exact prefixLift 5797774
  have htrace : WordTrace (prefixWord ++ tailWord_5797774) baseStart_5797774 baseEnd_5797774 := by
    simpa [prefixWord, tailWord_5797774, baseEnd_5797774] using wordTrace_append hprefix tailTrace_5797774
  have hstable : (prefixWord ++ tailWord_5797774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797774).length < 2 ^ (prefixWord ++ tailWord_5797774).sum := by decide
  have hdescent : baseEnd_5797774 < baseStart_5797774 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797777 : List Nat := [1, 2, 2, 1, 1, 1, 6, 3, 2, 1, 3]
def baseStart_5797777 : Nat := 118140960795 + 5797777 * 2 ^ 59
def prefixEnd_5797777 : Nat := 4983230072969 + 3 ^ 40 * 5797777 * 2
def baseEnd_5797777 : Nat := 2977046328582467904524015

theorem tailTrace_5797777 : CollatzResearch.WordTrace tailWord_5797777 prefixEnd_5797777 2977046328582467904524015 := by
  unfold tailWord_5797777
  simp only [CollatzResearch.WordTrace]
  refine ⟨211462299516651585324335585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140974866344434390216223723 211462299516651585324335585)
  ·
    refine ⟨158596724637488688993251689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211462299516651585324335585 158596724637488688993251689)
    ·
      refine ⟨118947543478116516744938767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158596724637488688993251689 118947543478116516744938767)
      ·
        refine ⟨178421315217174775117408151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118947543478116516744938767 178421315217174775117408151)
        ·
          refine ⟨267631972825762162676112227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178421315217174775117408151 267631972825762162676112227)
          ·
            refine ⟨401447959238643244014168341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267631972825762162676112227 401447959238643244014168341)
            ·
              refine ⟨18817873089311402063164141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 401447959238643244014168341 18817873089311402063164141)
              ·
                refine ⟨7056702408491775773686553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18817873089311402063164141 7056702408491775773686553)
                ·
                  refine ⟨5292526806368831830264915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7056702408491775773686553 5292526806368831830264915)
                  ·
                    refine ⟨7938790209553247745397373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5292526806368831830264915 7938790209553247745397373)
                    ·
                      refine ⟨2977046328582467904524015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7938790209553247745397373 2977046328582467904524015)
                      ·
                        rfl

theorem cell23_5797777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 3, 2, 1, 3].length) (baseStart_5797777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797777 prefixEnd_5797777 := by exact prefixLift 5797777
  have htrace : WordTrace (prefixWord ++ tailWord_5797777) baseStart_5797777 baseEnd_5797777 := by
    simpa [prefixWord, tailWord_5797777, baseEnd_5797777] using wordTrace_append hprefix tailTrace_5797777
  have hstable : (prefixWord ++ tailWord_5797777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797777).length < 2 ^ (prefixWord ++ tailWord_5797777).sum := by decide
  have hdescent : baseEnd_5797777 < baseStart_5797777 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797834 : List Nat := [3, 1, 2, 1, 2, 1, 2, 5, 2, 2, 2]
def baseStart_5797834 : Nat := 118140960795 + 5797834 * 2 ^ 59
def prefixEnd_5797834 : Nat := 4983230072969 + 3 ^ 40 * 5797834 * 2
def baseEnd_5797834 : Nat := 2977075596979774181511253

theorem tailTrace_5797834 : CollatzResearch.WordTrace tailWord_5797834 prefixEnd_5797834 2977075596979774181511253 := by
  unfold tailWord_5797834
  simp only [CollatzResearch.WordTrace]
  refine ⟨52866094619361271014790139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140976252318296722706107037 52866094619361271014790139)
  ·
    refine ⟨79299141929041906522185209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52866094619361271014790139 79299141929041906522185209)
    ·
      refine ⟨59474356446781429891638907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79299141929041906522185209 59474356446781429891638907)
      ·
        refine ⟨89211534670172144837458361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59474356446781429891638907 89211534670172144837458361)
        ·
          refine ⟨66908651002629108628093771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89211534670172144837458361 66908651002629108628093771)
          ·
            refine ⟨100362976503943662942140657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66908651002629108628093771 100362976503943662942140657)
            ·
              refine ⟨75272232377957747206605493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100362976503943662942140657 75272232377957747206605493)
              ·
                refine ⟨7056771785433538800619265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75272232377957747206605493 7056771785433538800619265)
                ·
                  refine ⟨5292578839075154100464449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7056771785433538800619265 5292578839075154100464449)
                  ·
                    refine ⟨3969434129306365575348337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5292578839075154100464449 3969434129306365575348337)
                    ·
                      refine ⟨2977075596979774181511253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3969434129306365575348337 2977075596979774181511253)
                      ·
                        rfl

theorem cell23_5797834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 5, 2, 2, 2].length) (baseStart_5797834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797834 prefixEnd_5797834 := by exact prefixLift 5797834
  have htrace : WordTrace (prefixWord ++ tailWord_5797834) baseStart_5797834 baseEnd_5797834 := by
    simpa [prefixWord, tailWord_5797834, baseEnd_5797834] using wordTrace_append hprefix tailTrace_5797834
  have hstable : (prefixWord ++ tailWord_5797834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797834).length < 2 ^ (prefixWord ++ tailWord_5797834).sum := by decide
  have hdescent : baseEnd_5797834 < baseStart_5797834 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797857 : List Nat := [1, 2, 3, 1, 2, 1, 5, 3, 5]
def baseStart_5797857 : Nat := 118140960795 + 5797857 * 2 ^ 59
def prefixEnd_5797857 : Nat := 4983230072969 + 3 ^ 40 * 5797857 * 2
def baseEnd_5797857 : Nat := 330787489670536399058183

theorem tailTrace_5797857 : CollatzResearch.WordTrace tailWord_5797857 prefixEnd_5797857 330787489670536399058183 := by
  unfold tailWord_5797857
  simp only [CollatzResearch.WordTrace]
  refine ⟨211465217356361758987247825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140976811570907839324831883 211465217356361758987247825)
  ·
    refine ⟨158598913017271319240435869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211465217356361758987247825 158598913017271319240435869)
    ·
      refine ⟨59474592381476744715163451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158598913017271319240435869 59474592381476744715163451)
      ·
        refine ⟨89211888572215117072745177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59474592381476744715163451 89211888572215117072745177)
        ·
          refine ⟨66908916429161337804558883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89211888572215117072745177 66908916429161337804558883)
          ·
            refine ⟨100363374643742006706838325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66908916429161337804558883 100363374643742006706838325)
            ·
              refine ⟨9409066372850813128766093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 100363374643742006706838325 9409066372850813128766093)
              ·
                refine ⟨3528399889819054923287285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9409066372850813128766093 3528399889819054923287285)
                ·
                  refine ⟨330787489670536399058183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3528399889819054923287285 330787489670536399058183)
                  ·
                    rfl

theorem cell23_5797857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 3, 5].length) (baseStart_5797857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797857 prefixEnd_5797857 := by exact prefixLift 5797857
  have htrace : WordTrace (prefixWord ++ tailWord_5797857) baseStart_5797857 baseEnd_5797857 := by
    simpa [prefixWord, tailWord_5797857, baseEnd_5797857] using wordTrace_append hprefix tailTrace_5797857
  have hstable : (prefixWord ++ tailWord_5797857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797857).length < 2 ^ (prefixWord ++ tailWord_5797857).sum := by decide
  have hdescent : baseEnd_5797857 < baseStart_5797857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797967 : List Nat := [1, 1, 2, 1, 1, 2, 2, 5, 1, 5, 2]
def baseStart_5797967 : Nat := 118140960795 + 5797967 * 2 ^ 59
def prefixEnd_5797967 : Nat := 4983230072969 + 3 ^ 40 * 5797967 * 2
def baseEnd_5797967 : Nat := 2977143889906822161148141

theorem tailTrace_5797967 : CollatzResearch.WordTrace tailWord_5797967 prefixEnd_5797967 2977143889906822161148141 := by
  unfold tailWord_5797967
  simp only [CollatzResearch.WordTrace]
  refine ⟨211469229385963247773752155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140979486257308831849168103 211469229385963247773752155)
  ·
    refine ⟨317203844078944871660628233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211469229385963247773752155 317203844078944871660628233)
    ·
      refine ⟨237902883059208653745471175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317203844078944871660628233 237902883059208653745471175)
      ·
        refine ⟨356854324588812980618206763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237902883059208653745471175 356854324588812980618206763)
        ·
          refine ⟨535281486883219470927310145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356854324588812980618206763 535281486883219470927310145)
          ·
            refine ⟨401461115162414603195482609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 535281486883219470927310145 401461115162414603195482609)
            ·
              refine ⟨301095836371810952396611957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 401461115162414603195482609 301095836371810952396611957)
              ·
                refine ⟨28227734659857276787182371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 301095836371810952396611957 28227734659857276787182371)
                ·
                  refine ⟨42341601989785915180773557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28227734659857276787182371 42341601989785915180773557)
                  ·
                    refine ⟨3969525186542429548197521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42341601989785915180773557 3969525186542429548197521)
                    ·
                      refine ⟨2977143889906822161148141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3969525186542429548197521 2977143889906822161148141)
                      ·
                        rfl

theorem cell23_5797967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 5, 2].length) (baseStart_5797967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797967 prefixEnd_5797967 := by exact prefixLift 5797967
  have htrace : WordTrace (prefixWord ++ tailWord_5797967) baseStart_5797967 baseEnd_5797967 := by
    simpa [prefixWord, tailWord_5797967, baseEnd_5797967] using wordTrace_append hprefix tailTrace_5797967
  have hstable : (prefixWord ++ tailWord_5797967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797967).length < 2 ^ (prefixWord ++ tailWord_5797967).sum := by decide
  have hdescent : baseEnd_5797967 < baseStart_5797967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797977 : List Nat := [1, 2, 1, 2, 2, 1, 5, 3, 1, 5]
def baseStart_5797977 : Nat := 118140960795 + 5797977 * 2 ^ 59
def prefixEnd_5797977 : Nat := 4983230072969 + 3 ^ 40 * 5797977 * 2
def baseEnd_5797977 : Nat := 992383008237789040674365

theorem tailTrace_5797977 : CollatzResearch.WordTrace tailWord_5797977 prefixEnd_5797977 992383008237789040674365 := by
  unfold tailWord_5797977
  simp only [CollatzResearch.WordTrace]
  refine ⟨211469594115927019481616185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140979729410618012987744123 211469594115927019481616185)
  ·
    refine ⟨158602195586945264611212139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211469594115927019481616185 158602195586945264611212139)
    ·
      refine ⟨237903293380417896916818209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158602195586945264611212139 237903293380417896916818209)
      ·
        refine ⟨178427470035313422687613657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237903293380417896916818209 178427470035313422687613657)
        ·
          refine ⟨133820602526485067015710243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178427470035313422687613657 133820602526485067015710243)
          ·
            refine ⟨200730903789727600523565365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133820602526485067015710243 200730903789727600523565365)
            ·
              refine ⟨18818522230286962549084253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 200730903789727600523565365 18818522230286962549084253)
              ·
                refine ⟨7056945836357610955906595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18818522230286962549084253 7056945836357610955906595)
                ·
                  refine ⟨10585418754536416433859893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7056945836357610955906595 10585418754536416433859893)
                  ·
                    refine ⟨992383008237789040674365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10585418754536416433859893 992383008237789040674365)
                    ·
                      rfl

theorem cell23_5797977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 3, 1, 5].length) (baseStart_5797977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797977 prefixEnd_5797977 := by exact prefixLift 5797977
  have htrace : WordTrace (prefixWord ++ tailWord_5797977) baseStart_5797977 baseEnd_5797977 := by
    simpa [prefixWord, tailWord_5797977, baseEnd_5797977] using wordTrace_append hprefix tailTrace_5797977
  have hstable : (prefixWord ++ tailWord_5797977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797977).length < 2 ^ (prefixWord ++ tailWord_5797977).sum := by decide
  have hdescent : baseEnd_5797977 < baseStart_5797977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797981 : List Nat := [1, 4, 4, 1, 1, 3, 1, 2, 6]
def baseStart_5797981 : Nat := 118140960795 + 5797981 * 2 ^ 59
def prefixEnd_5797981 : Nat := 4983230072969 + 3 ^ 40 * 5797981 * 2
def baseEnd_5797981 : Nat := 330794564292887234041453

theorem tailTrace_5797981 : CollatzResearch.WordTrace tailWord_5797981 prefixEnd_5797981 330794564292887234041453 := by
  unfold tailWord_5797981
  simp only [CollatzResearch.WordTrace]
  refine ⟨211469740007912528164761797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140979826671941685443174531 211469740007912528164761797)
  ·
    refine ⟨39650576251483599030892837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 211469740007912528164761797 39650576251483599030892837)
    ·
      refine ⟨7434483047153174818292407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39650576251483599030892837 7434483047153174818292407)
      ·
        refine ⟨11151724570729762227438611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7434483047153174818292407 11151724570729762227438611)
        ·
          refine ⟨16727586856094643341157917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11151724570729762227438611 16727586856094643341157917)
          ·
            refine ⟨6272845071035491252934219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16727586856094643341157917 6272845071035491252934219)
            ·
              refine ⟨9409267606553236879401329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6272845071035491252934219 9409267606553236879401329)
              ·
                refine ⟨7056950704914927659550997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9409267606553236879401329 7056950704914927659550997)
                ·
                  refine ⟨330794564292887234041453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7056950704914927659550997 330794564292887234041453)
                  ·
                    rfl

theorem cell23_5797981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 2, 6].length) (baseStart_5797981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797981 prefixEnd_5797981 := by exact prefixLift 5797981
  have htrace : WordTrace (prefixWord ++ tailWord_5797981) baseStart_5797981 baseEnd_5797981 := by
    simpa [prefixWord, tailWord_5797981, baseEnd_5797981] using wordTrace_append hprefix tailTrace_5797981
  have hstable : (prefixWord ++ tailWord_5797981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797981).length < 2 ^ (prefixWord ++ tailWord_5797981).sum := by decide
  have hdescent : baseEnd_5797981 < baseStart_5797981 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5797991 : List Nat := [1, 1, 5, 1, 1, 2, 1, 6, 1, 1, 3]
def baseStart_5797991 : Nat := 118140960795 + 5797991 * 2 ^ 59
def prefixEnd_5797991 : Nat := 4983230072969 + 3 ^ 40 * 5797991 * 2
def baseEnd_5797991 : Nat := 2977156213442530067248031

theorem tailTrace_5797991 : CollatzResearch.WordTrace tailWord_5797991 prefixEnd_5797991 2977156213442530067248031 := by
  unfold tailWord_5797991
  simp only [CollatzResearch.WordTrace]
  refine ⟨211470104737876299872625827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140980069825250866581750551 211470104737876299872625827)
  ·
    refine ⟨317205157106814449808938741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211470104737876299872625827 317205157106814449808938741)
    ·
      refine ⟨29737983478763854669588007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 317205157106814449808938741 29737983478763854669588007)
      ·
        refine ⟨44606975218145782004382011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29737983478763854669588007 44606975218145782004382011)
        ·
          refine ⟨66910462827218673006573017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44606975218145782004382011 66910462827218673006573017)
          ·
            refine ⟨50182847120414004754929763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66910462827218673006573017 50182847120414004754929763)
            ·
              refine ⟨75274270680621007132394645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50182847120414004754929763 75274270680621007132394645)
              ·
                refine ⟨3528481438154109709330999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 75274270680621007132394645 3528481438154109709330999)
                ·
                  refine ⟨5292722157231164563996499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3528481438154109709330999 5292722157231164563996499)
                  ·
                    refine ⟨7939083235846746845994749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5292722157231164563996499 7939083235846746845994749)
                    ·
                      refine ⟨2977156213442530067248031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7939083235846746845994749 2977156213442530067248031)
                      ·
                        rfl

theorem cell23_5797991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 6, 1, 1, 3].length) (baseStart_5797991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5797991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5797991 prefixEnd_5797991 := by exact prefixLift 5797991
  have htrace : WordTrace (prefixWord ++ tailWord_5797991) baseStart_5797991 baseEnd_5797991 := by
    simpa [prefixWord, tailWord_5797991, baseEnd_5797991] using wordTrace_append hprefix tailTrace_5797991
  have hstable : (prefixWord ++ tailWord_5797991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5797991).length < 2 ^ (prefixWord ++ tailWord_5797991).sum := by decide
  have hdescent : baseEnd_5797991 < baseStart_5797991 := by decide
  rcases family_descends (prefixWord ++ tailWord_5797991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5798007 : List Nat := [1, 1, 3, 1, 1, 5, 3, 1, 1, 6]
def baseStart_5798007 : Nat := 118140960795 + 5798007 * 2 ^ 59
def prefixEnd_5798007 : Nat := 4983230072969 + 3 ^ 40 * 5798007 * 2
def baseEnd_5798007 : Nat := 992388143044334001549319

theorem tailTrace_5798007 : CollatzResearch.WordTrace tailWord_5798007 prefixEnd_5798007 992388143044334001549319 := by
  unfold tailWord_5798007
  simp only [CollatzResearch.WordTrace]
  refine ⟨211470688305818334605208275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140980458870545556403472183 211470688305818334605208275)
  ·
    refine ⟨317206032458727501907812413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211470688305818334605208275 317206032458727501907812413)
    ·
      refine ⟨118952262172022813215429655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 317206032458727501907812413 118952262172022813215429655)
      ·
        refine ⟨178428393258034219823144483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118952262172022813215429655 178428393258034219823144483)
        ·
          refine ⟨267642589887051329734716725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178428393258034219823144483 267642589887051329734716725)
          ·
            refine ⟨25091492801911062162629693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 267642589887051329734716725 25091492801911062162629693)
            ·
              refine ⟨9409309800716648310986135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25091492801911062162629693 9409309800716648310986135)
              ·
                refine ⟨14113964701074972466479203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9409309800716648310986135 14113964701074972466479203)
                ·
                  refine ⟨21170947051612458699718805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14113964701074972466479203 21170947051612458699718805)
                  ·
                    refine ⟨992388143044334001549319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21170947051612458699718805 992388143044334001549319)
                    ·
                      rfl

theorem cell23_5798007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 6].length) (baseStart_5798007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5798007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5798007 prefixEnd_5798007 := by exact prefixLift 5798007
  have htrace : WordTrace (prefixWord ++ tailWord_5798007) baseStart_5798007 baseEnd_5798007 := by
    simpa [prefixWord, tailWord_5798007, baseEnd_5798007] using wordTrace_append hprefix tailTrace_5798007
  have hstable : (prefixWord ++ tailWord_5798007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5798007).length < 2 ^ (prefixWord ++ tailWord_5798007).sum := by decide
  have hdescent : baseEnd_5798007 < baseStart_5798007 := by decide
  rcases family_descends (prefixWord ++ tailWord_5798007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5798024 : List Nat := [2, 1, 3, 4, 1, 1, 1, 2, 4, 4]
def baseStart_5798024 : Nat := 118140960795 + 5798024 * 2 ^ 59
def prefixEnd_5798024 : Nat := 4983230072969 + 3 ^ 40 * 5798024 * 2
def baseEnd_5798024 : Nat := 992391052768042812711793

theorem tailTrace_5798024 : CollatzResearch.WordTrace tailWord_5798024 prefixEnd_5798024 992391052768042812711793 := by
  unfold tailWord_5798024
  simp only [CollatzResearch.WordTrace]
  refine ⟨105735654173378373254288563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140980872231171164339051417 105735654173378373254288563)
  ·
    refine ⟨158603481260067559881432845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105735654173378373254288563 158603481260067559881432845)
    ·
      refine ⟨59476305472525334955537317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158603481260067559881432845 59476305472525334955537317)
      ·
        refine ⟨11151807276098500304163247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59476305472525334955537317 11151807276098500304163247)
        ·
          refine ⟨16727710914147750456244871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11151807276098500304163247 16727710914147750456244871)
          ·
            refine ⟨25091566371221625684367307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16727710914147750456244871 25091566371221625684367307)
            ·
              refine ⟨37637349556832438526550961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25091566371221625684367307 37637349556832438526550961)
              ·
                refine ⟨28228012167624328894913221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37637349556832438526550961 28228012167624328894913221)
                ·
                  refine ⟨5292752281429561667796229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28228012167624328894913221 5292752281429561667796229)
                  ·
                    refine ⟨992391052768042812711793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5292752281429561667796229 992391052768042812711793)
                    ·
                      rfl

theorem cell23_5798024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 4, 4].length) (baseStart_5798024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5798024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5798024 prefixEnd_5798024 := by exact prefixLift 5798024
  have htrace : WordTrace (prefixWord ++ tailWord_5798024) baseStart_5798024 baseEnd_5798024 := by
    simpa [prefixWord, tailWord_5798024, baseEnd_5798024] using wordTrace_append hprefix tailTrace_5798024
  have hstable : (prefixWord ++ tailWord_5798024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5798024).length < 2 ^ (prefixWord ++ tailWord_5798024).sum := by decide
  have hdescent : baseEnd_5798024 < baseStart_5798024 := by decide
  rcases family_descends (prefixWord ++ tailWord_5798024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5798034 : List Nat := [3, 2, 3, 1, 1, 1, 4, 1, 1, 1, 5]
def baseStart_5798034 : Nat := 118140960795 + 5798034 * 2 ^ 59
def prefixEnd_5798034 : Nat := 4983230072969 + 3 ^ 40 * 5798034 * 2
def baseEnd_5798034 : Nat := 2977178293110673399010333

theorem tailTrace_5798034 : CollatzResearch.WordTrace tailWord_5798034 prefixEnd_5798034 2977178293110673399010333 := by
  unfold tailWord_5798034
  simp only [CollatzResearch.WordTrace]
  refine ⟨52867918269180129554110289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140981115384480345477627437 52867918269180129554110289)
  ·
    refine ⟨39650938701885097165582717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52867918269180129554110289 39650938701885097165582717)
    ·
      refine ⟨14869102013206911437093519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39650938701885097165582717 14869102013206911437093519)
      ·
        refine ⟨22303653019810367155640279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14869102013206911437093519 22303653019810367155640279)
        ·
          refine ⟨33455479529715550733460419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22303653019810367155640279 33455479529715550733460419)
          ·
            refine ⟨50183219294573326100190629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33455479529715550733460419 50183219294573326100190629)
            ·
              refine ⟨9409353617732498643785743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50183219294573326100190629 9409353617732498643785743)
              ·
                refine ⟨14114030426598747965678615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9409353617732498643785743 14114030426598747965678615)
                ·
                  refine ⟨21171045639898121948517923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14114030426598747965678615 21171045639898121948517923)
                  ·
                    refine ⟨31756568459847182922776885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21171045639898121948517923 31756568459847182922776885)
                    ·
                      refine ⟨2977178293110673399010333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31756568459847182922776885 2977178293110673399010333)
                      ·
                        rfl

theorem cell23_5798034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_5798034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5798034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5798034 prefixEnd_5798034 := by exact prefixLift 5798034
  have htrace : WordTrace (prefixWord ++ tailWord_5798034) baseStart_5798034 baseEnd_5798034 := by
    simpa [prefixWord, tailWord_5798034, baseEnd_5798034] using wordTrace_append hprefix tailTrace_5798034
  have hstable : (prefixWord ++ tailWord_5798034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5798034).length < 2 ^ (prefixWord ++ tailWord_5798034).sum := by decide
  have hdescent : baseEnd_5798034 < baseStart_5798034 := by decide
  rcases family_descends (prefixWord ++ tailWord_5798034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5798048 : List Nat := [2, 1, 1, 4, 2, 4, 1, 1, 3, 2, 2]
def baseStart_5798048 : Nat := 118140960795 + 5798048 * 2 ^ 59
def prefixEnd_5798048 : Nat := 4983230072969 + 3 ^ 40 * 5798048 * 2
def baseEnd_5798048 : Nat := 2977185481839836344235269

theorem tailTrace_5798048 : CollatzResearch.WordTrace tailWord_5798048 prefixEnd_5798048 2977185481839836344235269 := by
  unfold tailWord_5798048
  simp only [CollatzResearch.WordTrace]
  refine ⟨105736091849334899303725399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140981455799113199071633865 105736091849334899303725399)
  ·
    refine ⟨158604137774002348955588099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105736091849334899303725399 158604137774002348955588099)
    ·
      refine ⟨237906206661003523433382149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158604137774002348955588099 237906206661003523433382149)
      ·
        refine ⟨44607413748938160643759153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 237906206661003523433382149 44607413748938160643759153)
        ·
          refine ⟨33455560311703620482819365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44607413748938160643759153 33455560311703620482819365)
          ·
            refine ⟨6272917558444428840528631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33455560311703620482819365 6272917558444428840528631)
            ·
              refine ⟨9409376337666643260792947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6272917558444428840528631 9409376337666643260792947)
              ·
                refine ⟨14114064506499964891189421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9409376337666643260792947 14114064506499964891189421)
                ·
                  refine ⟨5292774189937486834196033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14114064506499964891189421 5292774189937486834196033)
                  ·
                    refine ⟨3969580642453115125647025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5292774189937486834196033 3969580642453115125647025)
                    ·
                      refine ⟨2977185481839836344235269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3969580642453115125647025 2977185481839836344235269)
                      ·
                        rfl

theorem cell23_5798048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 3, 2, 2].length) (baseStart_5798048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5798048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5798048 prefixEnd_5798048 := by exact prefixLift 5798048
  have htrace : WordTrace (prefixWord ++ tailWord_5798048) baseStart_5798048 baseEnd_5798048 := by
    simpa [prefixWord, tailWord_5798048, baseEnd_5798048] using wordTrace_append hprefix tailTrace_5798048
  have hstable : (prefixWord ++ tailWord_5798048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5798048).length < 2 ^ (prefixWord ++ tailWord_5798048).sum := by decide
  have hdescent : baseEnd_5798048 < baseStart_5798048 := by decide
  rcases family_descends (prefixWord ++ tailWord_5798048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5798058 : List Nat := [3, 1, 5, 1, 2, 1, 1, 3, 2, 4]
def baseStart_5798058 : Nat := 118140960795 + 5798058 * 2 ^ 59
def prefixEnd_5798058 : Nat := 4983230072969 + 3 ^ 40 * 5798058 * 2
def baseEnd_5798058 : Nat := 992396872215460435036741

theorem tailTrace_5798058 : CollatzResearch.WordTrace tailWord_5798058 prefixEnd_5798058 992396872215460435036741 := by
  unfold tailWord_5798058
  simp only [CollatzResearch.WordTrace]
  refine ⟨52868137107158392578828707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140981698952422380210209885 52868137107158392578828707)
  ·
    refine ⟨79302205660737588868243061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52868137107158392578828707 79302205660737588868243061)
    ·
      refine ⟨7434581780694148956397787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79302205660737588868243061 7434581780694148956397787)
      ·
        refine ⟨11151872671041223434596681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7434581780694148956397787 11151872671041223434596681)
        ·
          refine ⟨8363904503280917575947511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11151872671041223434596681 8363904503280917575947511)
          ·
            refine ⟨12545856754921376363921267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8363904503280917575947511 12545856754921376363921267)
            ·
              refine ⟨18818785132382064545881901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12545856754921376363921267 18818785132382064545881901)
              ·
                refine ⟨7057044424643274204705713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18818785132382064545881901 7057044424643274204705713)
                ·
                  refine ⟨5292783318482455653529285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7057044424643274204705713 5292783318482455653529285)
                  ·
                    refine ⟨992396872215460435036741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5292783318482455653529285 992396872215460435036741)
                    ·
                      rfl

theorem cell23_5798058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_5798058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5798058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5798058 prefixEnd_5798058 := by exact prefixLift 5798058
  have htrace : WordTrace (prefixWord ++ tailWord_5798058) baseStart_5798058 baseEnd_5798058 := by
    simpa [prefixWord, tailWord_5798058, baseEnd_5798058] using wordTrace_append hprefix tailTrace_5798058
  have hstable : (prefixWord ++ tailWord_5798058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5798058).length < 2 ^ (prefixWord ++ tailWord_5798058).sum := by decide
  have hdescent : baseEnd_5798058 < baseStart_5798058 := by decide
  rcases family_descends (prefixWord ++ tailWord_5798058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5798098 : List Nat := [3, 2, 2, 2, 1, 3, 2, 2, 2, 1, 3]
def baseStart_5798098 : Nat := 118140960795 + 5798098 * 2 ^ 59
def prefixEnd_5798098 : Nat := 4983230072969 + 3 ^ 40 * 5798098 * 2
def baseEnd_5798098 : Nat := 2977211155872561148610039

theorem tailTrace_5798098 : CollatzResearch.WordTrace tailWord_5798098 prefixEnd_5798098 2977211155872561148610039 := by
  unfold tailWord_5798098
  simp only [CollatzResearch.WordTrace]
  refine ⟨52868501837122164286692737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140982671565659104764513965 52868501837122164286692737)
  ·
    refine ⟨39651376377841623215019553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52868501837122164286692737 39651376377841623215019553)
    ·
      refine ⟨29738532283381217411264665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39651376377841623215019553 29738532283381217411264665)
      ·
        refine ⟨22303899212535913058448499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29738532283381217411264665 22303899212535913058448499)
        ·
          refine ⟨33455848818803869587672749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22303899212535913058448499 33455848818803869587672749)
          ·
            refine ⟨12545943307051451095377281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33455848818803869587672749 12545943307051451095377281)
            ·
              refine ⟨9409457480288588321532961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12545943307051451095377281 9409457480288588321532961)
              ·
                refine ⟨7057093110216441241149721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9409457480288588321532961 7057093110216441241149721)
                ·
                  refine ⟨5292819832662330930862291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7057093110216441241149721 5292819832662330930862291)
                  ·
                    refine ⟨7939229748993496396293437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5292819832662330930862291 7939229748993496396293437)
                    ·
                      refine ⟨2977211155872561148610039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7939229748993496396293437 2977211155872561148610039)
                      ·
                        rfl

theorem cell23_5798098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_5798098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5798098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5798098 prefixEnd_5798098 := by exact prefixLift 5798098
  have htrace : WordTrace (prefixWord ++ tailWord_5798098) baseStart_5798098 baseEnd_5798098 := by
    simpa [prefixWord, tailWord_5798098, baseEnd_5798098] using wordTrace_append hprefix tailTrace_5798098
  have hstable : (prefixWord ++ tailWord_5798098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5798098).length < 2 ^ (prefixWord ++ tailWord_5798098).sum := by decide
  have hdescent : baseEnd_5798098 < baseStart_5798098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5798098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5798107 : List Nat := [1, 1, 1, 1, 1, 1, 1, 7, 2, 4, 3]
def baseStart_5798107 : Nat := 118140960795 + 5798107 * 2 ^ 59
def prefixEnd_5798107 : Nat := 4983230072969 + 3 ^ 40 * 5798107 * 2
def baseEnd_5798107 : Nat := 2977215777198451613397497

theorem tailTrace_5798107 : CollatzResearch.WordTrace tailWord_5798107 prefixEnd_5798107 2977215777198451613397497 := by
  unfold tailWord_5798107
  simp only [CollatzResearch.WordTrace]
  refine ⟨211474335605456051683848575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140982890403637367789232383 211474335605456051683848575)
  ·
    refine ⟨317211503408184077525772863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211474335605456051683848575 317211503408184077525772863)
    ·
      refine ⟨475817255112276116288659295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317211503408184077525772863 475817255112276116288659295)
      ·
        refine ⟨713725882668414174432988943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475817255112276116288659295 713725882668414174432988943)
        ·
          refine ⟨1070588824002621261649483415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 713725882668414174432988943 1070588824002621261649483415)
          ·
            refine ⟨1605883236003931892474225123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1070588824002621261649483415 1605883236003931892474225123)
            ·
              refine ⟨2408824854005897838711337685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1605883236003931892474225123 2408824854005897838711337685)
              ·
                refine ⟨56456832515763230594796977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2408824854005897838711337685 56456832515763230594796977)
                ·
                  refine ⟨42342624386822422946097733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56456832515763230594796977 42342624386822422946097733)
                  ·
                    refine ⟨7939242072529204302393325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42342624386822422946097733 7939242072529204302393325)
                    ·
                      refine ⟨2977215777198451613397497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7939242072529204302393325 2977215777198451613397497)
                      ·
                        rfl

theorem cell23_5798107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 4, 3].length) (baseStart_5798107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5798107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5798107 prefixEnd_5798107 := by exact prefixLift 5798107
  have htrace : WordTrace (prefixWord ++ tailWord_5798107) baseStart_5798107 baseEnd_5798107 := by
    simpa [prefixWord, tailWord_5798107, baseEnd_5798107] using wordTrace_append hprefix tailTrace_5798107
  have hstable : (prefixWord ++ tailWord_5798107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5798107).length < 2 ^ (prefixWord ++ tailWord_5798107).sum := by decide
  have hdescent : baseEnd_5798107 < baseStart_5798107 := by decide
  rcases family_descends (prefixWord ++ tailWord_5798107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5798127 : List Nat := [1, 1, 2, 1, 6, 1, 1, 1, 9]
def baseStart_5798127 : Nat := 118140960795 + 5798127 * 2 ^ 59
def prefixEnd_5798127 : Nat := 4983230072969 + 3 ^ 40 * 5798127 * 2
def baseEnd_5798127 : Nat := 330802894090171281683045

theorem tailTrace_5798127 : CollatzResearch.WordTrace tailWord_5798127 prefixEnd_5798127 330802894090171281683045 := by
  unfold tailWord_5798127
  simp only [CollatzResearch.WordTrace]
  refine ⟨211475065065383595099576635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140983376710255730066384423 211475065065383595099576635)
  ·
    refine ⟨317212597598075392649364953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211475065065383595099576635 317212597598075392649364953)
    ·
      refine ⟨237909448198556544487023715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317212597598075392649364953 237909448198556544487023715)
      ·
        refine ⟨356864172297834816730535573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237909448198556544487023715 356864172297834816730535573)
        ·
          refine ⟨16728008076461007034243855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 356864172297834816730535573 16728008076461007034243855)
          ·
            refine ⟨25092012114691510551365783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16728008076461007034243855 25092012114691510551365783)
            ·
              refine ⟨37638018172037265827048675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25092012114691510551365783 37638018172037265827048675)
              ·
                refine ⟨56457027258055898740573013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37638018172037265827048675 56457027258055898740573013)
                ·
                  refine ⟨330802894090171281683045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 56457027258055898740573013 330802894090171281683045)
                  ·
                    rfl

theorem cell23_5798127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 9].length) (baseStart_5798127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5798127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5798127 prefixEnd_5798127 := by exact prefixLift 5798127
  have htrace : WordTrace (prefixWord ++ tailWord_5798127) baseStart_5798127 baseEnd_5798127 := by
    simpa [prefixWord, tailWord_5798127, baseEnd_5798127] using wordTrace_append hprefix tailTrace_5798127
  have hstable : (prefixWord ++ tailWord_5798127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5798127).length < 2 ^ (prefixWord ++ tailWord_5798127).sum := by decide
  have hdescent : baseEnd_5798127 < baseStart_5798127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5798127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5798144 : List Nat := [2, 1, 1, 2, 1, 1, 5, 5, 5]
def baseStart_5798144 : Nat := 118140960795 + 5798144 * 2 ^ 59
def prefixEnd_5798144 : Nat := 4983230072969 + 3 ^ 40 * 5798144 * 2
def baseEnd_5798144 : Nat := 330803863998074218737203

theorem tailTrace_5798144 : CollatzResearch.WordTrace tailWord_5798144 prefixEnd_5798144 330803863998074218737203 := by
  unfold tailWord_5798144
  simp only [CollatzResearch.WordTrace]
  refine ⟨105737842553161003501472743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140983790070881338001963657 105737842553161003501472743)
  ·
    refine ⟨158606763829741505252209115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105737842553161003501472743 158606763829741505252209115)
    ·
      refine ⟨237910145744612257878313673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158606763829741505252209115 237910145744612257878313673)
      ·
        refine ⟨178432609308459193408735255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237910145744612257878313673 178432609308459193408735255)
        ·
          refine ⟨267648913962688790113102883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178432609308459193408735255 267648913962688790113102883)
          ·
            refine ⟨401473370944033185169654325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267648913962688790113102883 401473370944033185169654325)
            ·
              refine ⟨37638128526003111109655093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 401473370944033185169654325 37638128526003111109655093)
              ·
                refine ⟨3528574549312791666530165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37638128526003111109655093 3528574549312791666530165)
                ·
                  refine ⟨330803863998074218737203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3528574549312791666530165 330803863998074218737203)
                  ·
                    rfl

theorem cell23_5798144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 5, 5].length) (baseStart_5798144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5798144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5798144 prefixEnd_5798144 := by exact prefixLift 5798144
  have htrace : WordTrace (prefixWord ++ tailWord_5798144) baseStart_5798144 baseEnd_5798144 := by
    simpa [prefixWord, tailWord_5798144, baseEnd_5798144] using wordTrace_append hprefix tailTrace_5798144
  have hstable : (prefixWord ++ tailWord_5798144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5798144).length < 2 ^ (prefixWord ++ tailWord_5798144).sum := by decide
  have hdescent : baseEnd_5798144 < baseStart_5798144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5798144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5798154 : List Nat := [3, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3]
def baseStart_5798154 : Nat := 118140960795 + 5798154 * 2 ^ 59
def prefixEnd_5798154 : Nat := 4983230072969 + 3 ^ 40 * 5798154 * 2
def baseEnd_5798154 : Nat := 2977239910789212929509781

theorem tailTrace_5798154 : CollatzResearch.WordTrace tailWord_5798154 prefixEnd_5798154 2977239910789212929509781 := by
  unfold tailWord_5798154
  simp only [CollatzResearch.WordTrace]
  refine ⟨52869012459071444677702379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140984033224190519140539677 52869012459071444677702379)
  ·
    refine ⟨79303518688607167016553569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52869012459071444677702379 79303518688607167016553569)
    ·
      refine ⟨59477639016455375262415177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79303518688607167016553569 59477639016455375262415177)
      ·
        refine ⟨44608229262341531446811383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59477639016455375262415177 44608229262341531446811383)
        ·
          refine ⟨66912343893512297170217075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44608229262341531446811383 66912343893512297170217075)
          ·
            refine ⟨100368515840268445755325613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66912343893512297170217075 100368515840268445755325613)
            ·
              refine ⟨37638193440100667158247105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100368515840268445755325613 37638193440100667158247105)
              ·
                refine ⟨28228645080075500368685329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37638193440100667158247105 28228645080075500368685329)
                ·
                  refine ⟨21171483810056625276513997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28228645080075500368685329 21171483810056625276513997)
                  ·
                    refine ⟨7939306428771234478692749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21171483810056625276513997 7939306428771234478692749)
                    ·
                      refine ⟨2977239910789212929509781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7939306428771234478692749 2977239910789212929509781)
                      ·
                        rfl

theorem cell23_5798154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_5798154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5798154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5798154 prefixEnd_5798154 := by exact prefixLift 5798154
  have htrace : WordTrace (prefixWord ++ tailWord_5798154) baseStart_5798154 baseEnd_5798154 := by
    simpa [prefixWord, tailWord_5798154, baseEnd_5798154] using wordTrace_append hprefix tailTrace_5798154
  have hstable : (prefixWord ++ tailWord_5798154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5798154).length < 2 ^ (prefixWord ++ tailWord_5798154).sum := by decide
  have hdescent : baseEnd_5798154 < baseStart_5798154 := by decide
  rcases family_descends (prefixWord ++ tailWord_5798154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5798248 : List Nat := [2, 1, 4, 2, 2, 2, 2, 1, 2, 2, 3]
def baseStart_5798248 : Nat := 118140960795 + 5798248 * 2 ^ 59
def prefixEnd_5798248 : Nat := 4983230072969 + 3 ^ 40 * 5798248 * 2
def baseEnd_5798248 : Nat := 2977288177970735561734349

theorem tailTrace_5798248 : CollatzResearch.WordTrace tailWord_5798248 prefixEnd_5798248 2977288177970735561734349 := by
  unfold tailWord_5798248
  simp only [CollatzResearch.WordTrace]
  refine ⟨105739739148972616382365699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140986318865296821843154265 105739739148972616382365699)
  ·
    refine ⟨158609608723458924573548549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105739739148972616382365699 158609608723458924573548549)
    ·
      refine ⟨29739301635648548357540353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158609608723458924573548549 29739301635648548357540353)
      ·
        refine ⟨22304476226736411268155265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29739301635648548357540353 22304476226736411268155265)
        ·
          refine ⟨16728357170052308451116449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22304476226736411268155265 16728357170052308451116449)
          ·
            refine ⟨12546267877539231338337337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16728357170052308451116449 12546267877539231338337337)
            ·
              refine ⟨9409700908154423503753003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12546267877539231338337337 9409700908154423503753003)
              ·
                refine ⟨14114551362231635255629505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9409700908154423503753003 14114551362231635255629505)
                ·
                  refine ⟨10585913521673726441722129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14114551362231635255629505 10585913521673726441722129)
                  ·
                    refine ⟨7939435141255294831291597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10585913521673726441722129 7939435141255294831291597)
                    ·
                      refine ⟨2977288177970735561734349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7939435141255294831291597 2977288177970735561734349)
                      ·
                        rfl

theorem cell23_5798248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_5798248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5798248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5798248 prefixEnd_5798248 := by exact prefixLift 5798248
  have htrace : WordTrace (prefixWord ++ tailWord_5798248) baseStart_5798248 baseEnd_5798248 := by
    simpa [prefixWord, tailWord_5798248, baseEnd_5798248] using wordTrace_append hprefix tailTrace_5798248
  have hstable : (prefixWord ++ tailWord_5798248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5798248).length < 2 ^ (prefixWord ++ tailWord_5798248).sum := by decide
  have hdescent : baseEnd_5798248 < baseStart_5798248 := by decide
  rcases family_descends (prefixWord ++ tailWord_5798248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5798305 : List Nat := [1, 2, 3, 5, 1, 1, 1, 1, 1, 5, 2]
def baseStart_5798305 : Nat := 118140960795 + 5798305 * 2 ^ 59
def prefixEnd_5798305 : Nat := 4983230072969 + 3 ^ 40 * 5798305 * 2
def baseEnd_5798305 : Nat := 2977317446368041838721587

theorem tailTrace_5798305 : CollatzResearch.WordTrace tailWord_5798305 prefixEnd_5798305 2977317446368041838721587 := by
  unfold tailWord_5798305
  simp only [CollatzResearch.WordTrace]
  refine ⟨211481557258738731499556369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140987704839159154333037579 211481557258738731499556369)
  ·
    refine ⟨158611167944054048624667277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211481557258738731499556369 158611167944054048624667277)
    ·
      refine ⟨59479187979020268234250229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158611167944054048624667277 59479187979020268234250229)
      ·
        refine ⟨5576173873033150146960959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59479187979020268234250229 5576173873033150146960959)
        ·
          refine ⟨8364260809549725220441439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5576173873033150146960959 8364260809549725220441439)
          ·
            refine ⟨12546391214324587830662159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8364260809549725220441439 12546391214324587830662159)
            ·
              refine ⟨18819586821486881745993239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12546391214324587830662159 18819586821486881745993239)
              ·
                refine ⟨28229380232230322618989859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18819586821486881745993239 28229380232230322618989859)
                ·
                  refine ⟨42344070348345483928484789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28229380232230322618989859 42344070348345483928484789)
                  ·
                    refine ⟨3969756595157389118295449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42344070348345483928484789 3969756595157389118295449)
                    ·
                      refine ⟨2977317446368041838721587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3969756595157389118295449 2977317446368041838721587)
                      ·
                        rfl

theorem cell23_5798305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_5798305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5798305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5798305 prefixEnd_5798305 := by exact prefixLift 5798305
  have htrace : WordTrace (prefixWord ++ tailWord_5798305) baseStart_5798305 baseEnd_5798305 := by
    simpa [prefixWord, tailWord_5798305, baseEnd_5798305] using wordTrace_append hprefix tailTrace_5798305
  have hstable : (prefixWord ++ tailWord_5798305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5798305).length < 2 ^ (prefixWord ++ tailWord_5798305).sum := by decide
  have hdescent : baseEnd_5798305 < baseStart_5798305 := by decide
  rcases family_descends (prefixWord ++ tailWord_5798305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5798311 : List Nat := [1, 1, 6, 1, 1, 2, 2, 2, 1, 6]
def baseStart_5798311 : Nat := 118140960795 + 5798311 * 2 ^ 59
def prefixEnd_5798311 : Nat := 4983230072969 + 3 ^ 40 * 5798311 * 2
def baseEnd_5798311 : Nat := 992440175750656271748853

theorem tailTrace_5798311 : CollatzResearch.WordTrace tailWord_5798311 prefixEnd_5798311 992440175750656271748853 := by
  unfold tailWord_5798311
  simp only [CollatzResearch.WordTrace]
  refine ⟨211481776096716994524274787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140987850731144663016183191 211481776096716994524274787)
  ·
    refine ⟨317222664145075491786412181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211481776096716994524274787 317222664145075491786412181)
    ·
      refine ⟨14869812381800413677488071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 317222664145075491786412181 14869812381800413677488071)
      ·
        refine ⟨22304718572700620516232107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14869812381800413677488071 22304718572700620516232107)
        ·
          refine ⟨33457077859050930774348161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22304718572700620516232107 33457077859050930774348161)
          ·
            refine ⟨25092808394288198080761121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33457077859050930774348161 25092808394288198080761121)
            ·
              refine ⟨18819606295716148560570841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25092808394288198080761121 18819606295716148560570841)
              ·
                refine ⟨14114704721787111420428131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18819606295716148560570841 14114704721787111420428131)
                ·
                  refine ⟨21172057082680667130642197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14114704721787111420428131 21172057082680667130642197)
                  ·
                    refine ⟨992440175750656271748853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21172057082680667130642197 992440175750656271748853)
                    ·
                      rfl

theorem cell23_5798311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_5798311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5798311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5798311 prefixEnd_5798311 := by exact prefixLift 5798311
  have htrace : WordTrace (prefixWord ++ tailWord_5798311) baseStart_5798311 baseEnd_5798311 := by
    simpa [prefixWord, tailWord_5798311, baseEnd_5798311] using wordTrace_append hprefix tailTrace_5798311
  have hstable : (prefixWord ++ tailWord_5798311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5798311).length < 2 ^ (prefixWord ++ tailWord_5798311).sum := by decide
  have hdescent : baseEnd_5798311 < baseStart_5798311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5798311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5798312 : List Nat := [2, 1, 6, 1, 1, 1, 1, 5, 1, 1, 3]
def baseStart_5798312 : Nat := 118140960795 + 5798312 * 2 ^ 59
def prefixEnd_5798312 : Nat := 4983230072969 + 3 ^ 40 * 5798312 * 2
def baseEnd_5798312 : Nat := 2977321040732623311334055

theorem tailTrace_5798312 : CollatzResearch.WordTrace tailWord_5798312 prefixEnd_5798312 2977321040732623311334055 := by
  unfold tailWord_5798312
  simp only [CollatzResearch.WordTrace]
  refine ⟨105740906284856685847530595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140987875046475581130040793 105740906284856685847530595)
  ·
    refine ⟨158611359427285028771295893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105740906284856685847530595 158611359427285028771295893)
    ·
      refine ⟨7434907473153985723654495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 158611359427285028771295893 7434907473153985723654495)
      ·
        refine ⟨11152361209730978585481743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7434907473153985723654495 11152361209730978585481743)
        ·
          refine ⟨16728541814596467878222615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11152361209730978585481743 16728541814596467878222615)
          ·
            refine ⟨25092812721894701817333923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16728541814596467878222615 25092812721894701817333923)
            ·
              refine ⟨37639219082842052726000885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25092812721894701817333923 37639219082842052726000885)
              ·
                refine ⟨3528676789016442443062583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37639219082842052726000885 3528676789016442443062583)
                ·
                  refine ⟨5293015183524663664593875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3528676789016442443062583 5293015183524663664593875)
                  ·
                    refine ⟨7939522775286995496890813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5293015183524663664593875 7939522775286995496890813)
                    ·
                      refine ⟨2977321040732623311334055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7939522775286995496890813 2977321040732623311334055)
                      ·
                        rfl

theorem cell23_5798312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_5798312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5798312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5798312 prefixEnd_5798312 := by exact prefixLift 5798312
  have htrace : WordTrace (prefixWord ++ tailWord_5798312) baseStart_5798312 baseEnd_5798312 := by
    simpa [prefixWord, tailWord_5798312, baseEnd_5798312] using wordTrace_append hprefix tailTrace_5798312
  have hstable : (prefixWord ++ tailWord_5798312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5798312).length < 2 ^ (prefixWord ++ tailWord_5798312).sum := by decide
  have hdescent : baseEnd_5798312 < baseStart_5798312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5798312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5798386 : List Nat := [3, 2, 1, 4, 2, 1, 3, 2, 1, 2, 2]
def baseStart_5798386 : Nat := 118140960795 + 5798386 * 2 ^ 59
def prefixEnd_5798386 : Nat := 4983230072969 + 3 ^ 40 * 5798386 * 2
def baseEnd_5798386 : Nat := 2977359038301056021808715

theorem tailTrace_5798386 : CollatzResearch.WordTrace tailWord_5798386 prefixEnd_5798386 2977359038301056021808715 := by
  unfold tailWord_5798386
  simp only [CollatzResearch.WordTrace]
  refine ⟨52871127892861320583313753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140989674380963521555503341 52871127892861320583313753)
  ·
    refine ⟨39653345919645990437485315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52871127892861320583313753 39653345919645990437485315)
    ·
      refine ⟨59480018879468985656227973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39653345919645990437485315 59480018879468985656227973)
      ·
        refine ⟨11152503539900434810542745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59480018879468985656227973 11152503539900434810542745)
        ·
          refine ⟨8364377654925326107907059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11152503539900434810542745 8364377654925326107907059)
          ·
            refine ⟨12546566482387989161860589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8364377654925326107907059 12546566482387989161860589)
            ·
              refine ⟨4704962430895495935697721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12546566482387989161860589 4704962430895495935697721)
              ·
                refine ⟨3528721823171621951773291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4704962430895495935697721 3528721823171621951773291)
                ·
                  refine ⟨5293082734757432927659937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3528721823171621951773291 5293082734757432927659937)
                  ·
                    refine ⟨3969812051068074695744953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5293082734757432927659937 3969812051068074695744953)
                    ·
                      refine ⟨2977359038301056021808715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3969812051068074695744953 2977359038301056021808715)
                      ·
                        rfl

theorem cell23_5798386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_5798386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5798386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5798386 prefixEnd_5798386 := by exact prefixLift 5798386
  have htrace : WordTrace (prefixWord ++ tailWord_5798386) baseStart_5798386 baseEnd_5798386 := by
    simpa [prefixWord, tailWord_5798386, baseEnd_5798386] using wordTrace_append hprefix tailTrace_5798386
  have hstable : (prefixWord ++ tailWord_5798386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5798386).length < 2 ^ (prefixWord ++ tailWord_5798386).sum := by decide
  have hdescent : baseEnd_5798386 < baseStart_5798386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5798386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5798406 : List Nat := [6, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3]
def baseStart_5798406 : Nat := 118140960795 + 5798406 * 2 ^ 59
def prefixEnd_5798406 : Nat := 4983230072969 + 3 ^ 40 * 5798406 * 2
def baseEnd_5798406 : Nat := 2977369307914145943558623

theorem tailTrace_5798406 : CollatzResearch.WordTrace tailWord_5798406 prefixEnd_5798406 2977369307914145943558623 := by
  unfold tailWord_5798406
  simp only [CollatzResearch.WordTrace]
  refine ⟨6608913782230400804655721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 140990160687581883832655381 6608913782230400804655721)
  ·
    refine ⟨4956685336672800603491791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6608913782230400804655721 4956685336672800603491791)
    ·
      refine ⟨7435028005009200905237687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4956685336672800603491791 7435028005009200905237687)
      ·
        refine ⟨11152542007513801357856531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7435028005009200905237687 11152542007513801357856531)
        ·
          refine ⟨16728813011270702036784797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11152542007513801357856531 16728813011270702036784797)
          ·
            refine ⟨6273304879226513263794299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16728813011270702036784797 6273304879226513263794299)
            ·
              refine ⟨9409957318839769895691449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6273304879226513263794299 9409957318839769895691449)
              ·
                refine ⟨7057467989129827421768587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9409957318839769895691449 7057467989129827421768587)
                ·
                  refine ⟨10586201983694741132652881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7057467989129827421768587 10586201983694741132652881)
                  ·
                    refine ⟨7939651487771055849489661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10586201983694741132652881 7939651487771055849489661)
                    ·
                      refine ⟨2977369307914145943558623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7939651487771055849489661 2977369307914145943558623)
                      ·
                        rfl

theorem cell23_5798406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_5798406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5798406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5798406 prefixEnd_5798406 := by exact prefixLift 5798406
  have htrace : WordTrace (prefixWord ++ tailWord_5798406) baseStart_5798406 baseEnd_5798406 := by
    simpa [prefixWord, tailWord_5798406, baseEnd_5798406] using wordTrace_append hprefix tailTrace_5798406
  have hstable : (prefixWord ++ tailWord_5798406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5798406).length < 2 ^ (prefixWord ++ tailWord_5798406).sum := by decide
  have hdescent : baseEnd_5798406 < baseStart_5798406 := by decide
  rcases family_descends (prefixWord ++ tailWord_5798406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5798408 : List Nat := [2, 1, 3, 2, 1, 1, 1, 5, 1, 4, 2]
def baseStart_5798408 : Nat := 118140960795 + 5798408 * 2 ^ 59
def prefixEnd_5798408 : Nat := 4983230072969 + 3 ^ 40 * 5798408 * 2
def baseEnd_5798408 : Nat := 2977370334875454935733613

theorem tailTrace_5798408 : CollatzResearch.WordTrace tailWord_5798408 prefixEnd_5798408 2977370334875454935733613 := by
  unfold tailWord_5798408
  simp only [CollatzResearch.WordTrace]
  refine ⟨105742656988682790045277939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140990209318243720060370585 105742656988682790045277939)
  ·
    refine ⟨158613985483024185067916909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105742656988682790045277939 158613985483024185067916909)
    ·
      refine ⟨59480244556134069400468841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158613985483024185067916909 59480244556134069400468841)
      ·
        refine ⟨44610183417100552050351631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59480244556134069400468841 44610183417100552050351631)
        ·
          refine ⟨66915275125650828075527447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44610183417100552050351631 66915275125650828075527447)
          ·
            refine ⟨100372912688476242113291171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66915275125650828075527447 100372912688476242113291171)
            ·
              refine ⟨150559369032714363169936757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100372912688476242113291171 150559369032714363169936757)
              ·
                refine ⟨14114940846816971547181571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 150559369032714363169936757 14114940846816971547181571)
                ·
                  refine ⟨21172411270225457320772357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14114940846816971547181571 21172411270225457320772357)
                  ·
                    refine ⟨3969827113167273247644817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21172411270225457320772357 3969827113167273247644817)
                    ·
                      refine ⟨2977370334875454935733613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3969827113167273247644817 2977370334875454935733613)
                      ·
                        rfl

theorem cell23_5798408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 1, 4, 2].length) (baseStart_5798408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5798408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5798408 prefixEnd_5798408 := by exact prefixLift 5798408
  have htrace : WordTrace (prefixWord ++ tailWord_5798408) baseStart_5798408 baseEnd_5798408 := by
    simpa [prefixWord, tailWord_5798408, baseEnd_5798408] using wordTrace_append hprefix tailTrace_5798408
  have hstable : (prefixWord ++ tailWord_5798408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5798408).length < 2 ^ (prefixWord ++ tailWord_5798408).sum := by decide
  have hdescent : baseEnd_5798408 < baseStart_5798408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5798408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5798411 : List Nat := [1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 5]
def baseStart_5798411 : Nat := 118140960795 + 5798411 * 2 ^ 59
def prefixEnd_5798411 : Nat := 4983230072969 + 3 ^ 40 * 5798411 * 2
def baseEnd_5798411 : Nat := 2977371875317418423996099

theorem tailTrace_5798411 : CollatzResearch.WordTrace tailWord_5798411 prefixEnd_5798411 2977371875317418423996099 := by
  unfold tailWord_5798411
  simp only [CollatzResearch.WordTrace]
  refine ⟨211485423396354711602915087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140990282264236474401943391 211485423396354711602915087)
  ·
    refine ⟨317228135094532067404372631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211485423396354711602915087 317228135094532067404372631)
    ·
      refine ⟨475842202641798101106558947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317228135094532067404372631 475842202641798101106558947)
      ·
        refine ⟨713763303962697151659838421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475842202641798101106558947 713763303962697151659838421)
        ·
          refine ⟨16728827436625714492027463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 713763303962697151659838421 16728827436625714492027463)
          ·
            refine ⟨25093241154938571738041195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16728827436625714492027463 25093241154938571738041195)
            ·
              refine ⟨37639861732407857607061793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25093241154938571738041195 37639861732407857607061793)
              ·
                refine ⟨28229896299305893205296345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37639861732407857607061793 28229896299305893205296345)
                ·
                  refine ⟨21172422224479419903972259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28229896299305893205296345 21172422224479419903972259)
                  ·
                    refine ⟨31758633336719129855958389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21172422224479419903972259 31758633336719129855958389)
                    ·
                      refine ⟨2977371875317418423996099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31758633336719129855958389 2977371875317418423996099)
                      ·
                        rfl

theorem cell23_5798411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 5].length) (baseStart_5798411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5798411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5798411 prefixEnd_5798411 := by exact prefixLift 5798411
  have htrace : WordTrace (prefixWord ++ tailWord_5798411) baseStart_5798411 baseEnd_5798411 := by
    simpa [prefixWord, tailWord_5798411, baseEnd_5798411] using wordTrace_append hprefix tailTrace_5798411
  have hstable : (prefixWord ++ tailWord_5798411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5798411).length < 2 ^ (prefixWord ++ tailWord_5798411).sum := by decide
  have hdescent : baseEnd_5798411 < baseStart_5798411 := by decide
  rcases family_descends (prefixWord ++ tailWord_5798411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5798412 : List Nat := [2, 2, 1, 2, 4, 3, 1, 2, 1, 3, 2]
def baseStart_5798412 : Nat := 118140960795 + 5798412 * 2 ^ 59
def prefixEnd_5798412 : Nat := 4983230072969 + 3 ^ 40 * 5798412 * 2
def baseEnd_5798412 : Nat := 2977372388798072920083595

theorem tailTrace_5798412 : CollatzResearch.WordTrace tailWord_5798412 prefixEnd_5798412 2977372388798072920083595 := by
  unfold tailWord_5798412
  simp only [CollatzResearch.WordTrace]
  refine ⟨105742729934675544386850745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140990306579567392515800993 105742729934675544386850745)
  ·
    refine ⟨79307047451006658290138059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105742729934675544386850745 79307047451006658290138059)
    ·
      refine ⟨118960571176509987435207089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79307047451006658290138059 118960571176509987435207089)
      ·
        refine ⟨89220428382382490576405317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118960571176509987435207089 89220428382382490576405317)
        ·
          refine ⟨16728830321696716983075997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89220428382382490576405317 16728830321696716983075997)
          ·
            refine ⟨6273311370636268868653499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16728830321696716983075997 6273311370636268868653499)
            ·
              refine ⟨9409967055954403302980249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6273311370636268868653499 9409967055954403302980249)
              ·
                refine ⟨7057475291965802477235187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9409967055954403302980249 7057475291965802477235187)
                ·
                  refine ⟨10586212937948703715852781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7057475291965802477235187 10586212937948703715852781)
                  ·
                    refine ⟨3969829851730763893444793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10586212937948703715852781 3969829851730763893444793)
                    ·
                      refine ⟨2977372388798072920083595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3969829851730763893444793 2977372388798072920083595)
                      ·
                        rfl

theorem cell23_5798412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 2, 1, 3, 2].length) (baseStart_5798412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5798412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5798412 prefixEnd_5798412 := by exact prefixLift 5798412
  have htrace : WordTrace (prefixWord ++ tailWord_5798412) baseStart_5798412 baseEnd_5798412 := by
    simpa [prefixWord, tailWord_5798412, baseEnd_5798412] using wordTrace_append hprefix tailTrace_5798412
  have hstable : (prefixWord ++ tailWord_5798412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5798412).length < 2 ^ (prefixWord ++ tailWord_5798412).sum := by decide
  have hdescent : baseEnd_5798412 < baseStart_5798412 := by decide
  rcases family_descends (prefixWord ++ tailWord_5798412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5798442 : List Nat := [3, 1, 4, 1, 1, 2, 1, 4, 2, 2, 2]
def baseStart_5798442 : Nat := 118140960795 + 5798442 * 2 ^ 59
def prefixEnd_5798442 : Nat := 4983230072969 + 3 ^ 40 * 5798442 * 2
def baseEnd_5798442 : Nat := 2977387793217707802708457

theorem tailTrace_5798442 : CollatzResearch.WordTrace tailWord_5798442 prefixEnd_5798442 2977387793217707802708457 := by
  unfold tailWord_5798442
  simp only [CollatzResearch.WordTrace]
  refine ⟨52871638514810600974323395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140991036039494935931529053 52871638514810600974323395)
  ·
    refine ⟨79307457772215901461485093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52871638514810600974323395 79307457772215901461485093)
    ·
      refine ⟨14870148332290481524028455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79307457772215901461485093 14870148332290481524028455)
      ·
        refine ⟨22305222498435722286042683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14870148332290481524028455 22305222498435722286042683)
        ·
          refine ⟨33457833747653583429064025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22305222498435722286042683 33457833747653583429064025)
          ·
            refine ⟨25093375310740187571798019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33457833747653583429064025 25093375310740187571798019)
            ·
              refine ⟨37640062966110281357697029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25093375310740187571798019 37640062966110281357697029)
              ·
                refine ⟨7057511806145677754568193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37640062966110281357697029 7057511806145677754568193)
                ·
                  refine ⟨5293133854609258315926145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7057511806145677754568193 5293133854609258315926145)
                  ·
                    refine ⟨3969850390956943736944609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5293133854609258315926145 3969850390956943736944609)
                    ·
                      refine ⟨2977387793217707802708457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3969850390956943736944609 2977387793217707802708457)
                      ·
                        rfl

theorem cell23_5798442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_5798442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5798442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5798442 prefixEnd_5798442 := by exact prefixLift 5798442
  have htrace : WordTrace (prefixWord ++ tailWord_5798442) baseStart_5798442 baseEnd_5798442 := by
    simpa [prefixWord, tailWord_5798442, baseEnd_5798442] using wordTrace_append hprefix tailTrace_5798442
  have hstable : (prefixWord ++ tailWord_5798442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5798442).length < 2 ^ (prefixWord ++ tailWord_5798442).sum := by decide
  have hdescent : baseEnd_5798442 < baseStart_5798442 := by decide
  rcases family_descends (prefixWord ++ tailWord_5798442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5798458 : List Nat := [3, 1, 1, 1, 3, 4, 1, 1, 2, 3, 3]
def baseStart_5798458 : Nat := 118140960795 + 5798458 * 2 ^ 59
def prefixEnd_5798458 : Nat := 4983230072969 + 3 ^ 40 * 5798458 * 2
def baseEnd_5798458 : Nat := 2977396008908179740108383

theorem tailTrace_5798458 : CollatzResearch.WordTrace tailWord_5798458 prefixEnd_5798458 2977396008908179740108383 := by
  unfold tailWord_5798458
  simp only [CollatzResearch.WordTrace]
  refine ⟨52871784406796109657469007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140991425084789625753250685 52871784406796109657469007)
  ·
    refine ⟨79307676610194164486203511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52871784406796109657469007 79307676610194164486203511)
    ·
      refine ⟨118961514915291246729305267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79307676610194164486203511 118961514915291246729305267)
      ·
        refine ⟨178442272372936870093957901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118961514915291246729305267 178442272372936870093957901)
        ·
          refine ⟨66915852139851326285234213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178442272372936870093957901 66915852139851326285234213)
          ·
            refine ⟨12546722276222123678481415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66915852139851326285234213 12546722276222123678481415)
            ·
              refine ⟨18820083414333185517722123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12546722276222123678481415 18820083414333185517722123)
              ·
                refine ⟨28230125121499778276583185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18820083414333185517722123 28230125121499778276583185)
                ·
                  refine ⟨21172593841124833707437389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28230125121499778276583185 21172593841124833707437389)
                  ·
                    refine ⟨7939722690421812640289021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21172593841124833707437389 7939722690421812640289021)
                    ·
                      refine ⟨2977396008908179740108383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7939722690421812640289021 2977396008908179740108383)
                      ·
                        rfl

theorem cell23_5798458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 2, 3, 3].length) (baseStart_5798458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5798458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5798458 prefixEnd_5798458 := by exact prefixLift 5798458
  have htrace : WordTrace (prefixWord ++ tailWord_5798458) baseStart_5798458 baseEnd_5798458 := by
    simpa [prefixWord, tailWord_5798458, baseEnd_5798458] using wordTrace_append hprefix tailTrace_5798458
  have hstable : (prefixWord ++ tailWord_5798458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5798458).length < 2 ^ (prefixWord ++ tailWord_5798458).sum := by decide
  have hdescent : baseEnd_5798458 < baseStart_5798458 := by decide
  rcases family_descends (prefixWord ++ tailWord_5798458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5798478 : List Nat := [4, 1, 1, 1, 1, 2, 5, 1, 2, 5]
def baseStart_5798478 : Nat := 118140960795 + 5798478 * 2 ^ 59
def prefixEnd_5798478 : Nat := 4983230072969 + 3 ^ 40 * 5798478 * 2
def baseEnd_5798478 : Nat := 992468759507089887286097

theorem tailTrace_5798478 : CollatzResearch.WordTrace tailWord_5798478 prefixEnd_5798478 992468759507089887286097 := by
  unfold tailWord_5798478
  simp only [CollatzResearch.WordTrace]
  refine ⟨26435983385888997755700511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140991911391407988030402725 26435983385888997755700511)
  ·
    refine ⟨39653975078833496633550767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26435983385888997755700511 39653975078833496633550767)
    ·
      refine ⟨59480962618250244950326151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39653975078833496633550767 59480962618250244950326151)
      ·
        refine ⟨89221443927375367425489227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59480962618250244950326151 89221443927375367425489227)
        ·
          refine ⟨133832165891063051138233841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89221443927375367425489227 133832165891063051138233841)
          ·
            refine ⟨100374124418297288353675381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133832165891063051138233841 100374124418297288353675381)
            ·
              refine ⟨9410074164215370783157067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 100374124418297288353675381 9410074164215370783157067)
              ·
                refine ⟨14115111246323056174735601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9410074164215370783157067 14115111246323056174735601)
                ·
                  refine ⟨10586333434742292131051701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14115111246323056174735601 10586333434742292131051701)
                  ·
                    refine ⟨992468759507089887286097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10586333434742292131051701 992468759507089887286097)
                    ·
                      rfl

theorem cell23_5798478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 2, 5].length) (baseStart_5798478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5798478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5798478 prefixEnd_5798478 := by exact prefixLift 5798478
  have htrace : WordTrace (prefixWord ++ tailWord_5798478) baseStart_5798478 baseEnd_5798478 := by
    simpa [prefixWord, tailWord_5798478, baseEnd_5798478] using wordTrace_append hprefix tailTrace_5798478
  have hstable : (prefixWord ++ tailWord_5798478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5798478).length < 2 ^ (prefixWord ++ tailWord_5798478).sum := by decide
  have hdescent : baseEnd_5798478 < baseStart_5798478 := by decide
  rcases family_descends (prefixWord ++ tailWord_5798478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5798508 : List Nat := [2, 2, 1, 1, 3, 1, 3, 3, 3, 4]
def baseStart_5798508 : Nat := 118140960795 + 5798508 * 2 ^ 59
def prefixEnd_5798508 : Nat := 4983230072969 + 3 ^ 40 * 5798508 * 2
def baseEnd_5798508 : Nat := 992473894313634848161051

theorem tailTrace_5798508 : CollatzResearch.WordTrace tailWord_5798508 prefixEnd_5798508 992473894313634848161051 := by
  unfold tailWord_5798508
  simp only [CollatzResearch.WordTrace]
  refine ⟨105744480638501648584598089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140992640851335531446130785 105744480638501648584598089)
  ·
    refine ⟨79308360478876236438448567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105744480638501648584598089 79308360478876236438448567)
    ·
      refine ⟨118962540718314354657672851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79308360478876236438448567 118962540718314354657672851)
      ·
        refine ⟨178443811077471531986509277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118962540718314354657672851 178443811077471531986509277)
        ·
          refine ⟨66916429154051824494940979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178443811077471531986509277 66916429154051824494940979)
          ·
            refine ⟨100374643731077736742411469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66916429154051824494940979 100374643731077736742411469)
            ·
              refine ⟨37640491399154151278404301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100374643731077736742411469 37640491399154151278404301)
              ·
                refine ⟨14115184274682806729401613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37640491399154151278404301 14115184274682806729401613)
                ·
                  refine ⟨5293194103006052523525605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14115184274682806729401613 5293194103006052523525605)
                  ·
                    refine ⟨992473894313634848161051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5293194103006052523525605 992473894313634848161051)
                    ·
                      rfl

theorem cell23_5798508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 4].length) (baseStart_5798508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5798508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5798508 prefixEnd_5798508 := by exact prefixLift 5798508
  have htrace : WordTrace (prefixWord ++ tailWord_5798508) baseStart_5798508 baseEnd_5798508 := by
    simpa [prefixWord, tailWord_5798508, baseEnd_5798508] using wordTrace_append hprefix tailTrace_5798508
  have hstable : (prefixWord ++ tailWord_5798508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5798508).length < 2 ^ (prefixWord ++ tailWord_5798508).sum := by decide
  have hdescent : baseEnd_5798508 < baseStart_5798508 := by decide
  rcases family_descends (prefixWord ++ tailWord_5798508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5798592 : List Nat := [2, 1, 1, 2, 4, 3, 2, 1, 2, 3, 2]
def baseStart_5798592 : Nat := 118140960795 + 5798592 * 2 ^ 59
def prefixEnd_5798592 : Nat := 4983230072969 + 3 ^ 40 * 5798592 * 2
def baseEnd_5798592 : Nat := 2977464815315882215832767

theorem tailTrace_5798592 : CollatzResearch.WordTrace tailWord_5798592 prefixEnd_5798592 2977464815315882215832767 := by
  unfold tailWord_5798592
  simp only [CollatzResearch.WordTrace]
  refine ⟨105746012504349489757627015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140994683339132653010169353 105746012504349489757627015)
  ·
    refine ⟨158619018756524234636440523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105746012504349489757627015 158619018756524234636440523)
    ·
      refine ⟨237928528134786351954660785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158619018756524234636440523 237928528134786351954660785)
      ·
        refine ⟨178446396101089763965995589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237928528134786351954660785 178446396101089763965995589)
        ·
          refine ⟨33458699268954330743624173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 178446396101089763965995589 33458699268954330743624173)
          ·
            refine ⟨12547012225857874028859065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33458699268954330743624173 12547012225857874028859065)
            ·
              refine ⟨9410259169393405521644299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12547012225857874028859065 9410259169393405521644299)
              ·
                refine ⟨14115388754090108282466449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9410259169393405521644299 14115388754090108282466449)
                ·
                  refine ⟨10586541565567581211849837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14115388754090108282466449 10586541565567581211849837)
                  ·
                    refine ⟨3969953087087842954443689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10586541565567581211849837 3969953087087842954443689)
                    ·
                      refine ⟨2977464815315882215832767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3969953087087842954443689 2977464815315882215832767)
                      ·
                        rfl

theorem cell23_5798592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 2, 3, 2].length) (baseStart_5798592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5798592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5798592 prefixEnd_5798592 := by exact prefixLift 5798592
  have htrace : WordTrace (prefixWord ++ tailWord_5798592) baseStart_5798592 baseEnd_5798592 := by
    simpa [prefixWord, tailWord_5798592, baseEnd_5798592] using wordTrace_append hprefix tailTrace_5798592
  have hstable : (prefixWord ++ tailWord_5798592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5798592).length < 2 ^ (prefixWord ++ tailWord_5798592).sum := by decide
  have hdescent : baseEnd_5798592 < baseStart_5798592 := by decide
  rcases family_descends (prefixWord ++ tailWord_5798592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5798601 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 2, 5, 6]
def baseStart_5798601 : Nat := 118140960795 + 5798601 * 2 ^ 59
def prefixEnd_5798601 : Nat := 4983230072969 + 3 ^ 40 * 5798601 * 2
def baseEnd_5798601 : Nat := 2977469436641772680620225

theorem tailTrace_5798601 : CollatzResearch.WordTrace tailWord_5798601 prefixEnd_5798601 2977469436641772680620225 := by
  unfold tailWord_5798601
  simp only [CollatzResearch.WordTrace]
  refine ⟨211492353265666374052331657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140994902177110916034887771 211492353265666374052331657)
  ·
    refine ⟨158619264949249780539248743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211492353265666374052331657 158619264949249780539248743)
    ·
      refine ⟨237928897423874670808873115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158619264949249780539248743 237928897423874670808873115)
      ·
        refine ⟨356893346135812006213309673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237928897423874670808873115 356893346135812006213309673)
        ·
          refine ⟨267670009601859004659982255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 356893346135812006213309673 267670009601859004659982255)
          ·
            refine ⟨401505014402788506989973383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267670009601859004659982255 401505014402788506989973383)
            ·
              refine ⟨602257521604182760484960075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 401505014402788506989973383 602257521604182760484960075)
              ·
                refine ⟨903386282406274140727440113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 602257521604182760484960075 903386282406274140727440113)
                ·
                  refine ⟨677539711804705605545580085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 903386282406274140727440113 677539711804705605545580085)
                  ·
                    refine ⟨63519347981691150519898133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 677539711804705605545580085 63519347981691150519898133)
                    ·
                      refine ⟨2977469436641772680620225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63519347981691150519898133 2977469436641772680620225)
                      ·
                        rfl

theorem cell23_5798601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 5, 6].length) (baseStart_5798601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5798601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5798601 prefixEnd_5798601 := by exact prefixLift 5798601
  have htrace : WordTrace (prefixWord ++ tailWord_5798601) baseStart_5798601 baseEnd_5798601 := by
    simpa [prefixWord, tailWord_5798601, baseEnd_5798601] using wordTrace_append hprefix tailTrace_5798601
  have hstable : (prefixWord ++ tailWord_5798601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5798601).length < 2 ^ (prefixWord ++ tailWord_5798601).sum := by decide
  have hdescent : baseEnd_5798601 < baseStart_5798601 := by decide
  rcases family_descends (prefixWord ++ tailWord_5798601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5798602 : List Nat := [3, 1, 2, 1, 4, 2, 3, 1, 1, 5]
def baseStart_5798602 : Nat := 118140960795 + 5798602 * 2 ^ 59
def prefixEnd_5798602 : Nat := 4983230072969 + 3 ^ 40 * 5798602 * 2
def baseEnd_5798602 : Nat := 992489983374142392235907

theorem tailTrace_5798602 : CollatzResearch.WordTrace tailWord_5798602 prefixEnd_5798602 992489983374142392235907 := by
  unfold tailWord_5798602
  simp only [CollatzResearch.WordTrace]
  refine ⟨52873097434665687805779515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140994926492441834148745373 52873097434665687805779515)
  ·
    refine ⟨79309646151998531708669273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52873097434665687805779515 79309646151998531708669273)
    ·
      refine ⟨59482234613998898781501955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79309646151998531708669273 59482234613998898781501955)
      ·
        refine ⟨89223351920998348172252933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59482234613998898781501955 89223351920998348172252933)
        ·
          refine ⟨16729378485187190282297425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89223351920998348172252933 16729378485187190282297425)
          ·
            refine ⟨12547033863890392711723069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16729378485187190282297425 12547033863890392711723069)
            ·
              refine ⟨4705137698958897266896151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12547033863890392711723069 4705137698958897266896151)
              ·
                refine ⟨7057706548438345900344227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4705137698958897266896151 7057706548438345900344227)
                ·
                  refine ⟨10586559822657518850516341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7057706548438345900344227 10586559822657518850516341)
                  ·
                    refine ⟨992489983374142392235907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10586559822657518850516341 992489983374142392235907)
                    ·
                      rfl

theorem cell23_5798602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 1, 1, 5].length) (baseStart_5798602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5798602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5798602 prefixEnd_5798602 := by exact prefixLift 5798602
  have htrace : WordTrace (prefixWord ++ tailWord_5798602) baseStart_5798602 baseEnd_5798602 := by
    simpa [prefixWord, tailWord_5798602, baseEnd_5798602] using wordTrace_append hprefix tailTrace_5798602
  have hstable : (prefixWord ++ tailWord_5798602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5798602).length < 2 ^ (prefixWord ++ tailWord_5798602).sum := by decide
  have hdescent : baseEnd_5798602 < baseStart_5798602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5798602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5798615 : List Nat := [1, 1, 3, 2, 1, 4, 1, 4, 2, 4]
def baseStart_5798615 : Nat := 118140960795 + 5798615 * 2 ^ 59
def prefixEnd_5798615 : Nat := 4983230072969 + 3 ^ 40 * 5798615 * 2
def baseEnd_5798615 : Nat := 992492208456978541948387

theorem tailTrace_5798615 : CollatzResearch.WordTrace tailWord_5798615 prefixEnd_5798615 992492208456978541948387 := by
  unfold tailWord_5798615
  simp only [CollatzResearch.WordTrace]
  refine ⟨211492863887615654443341299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140995242591743769628894199 211492863887615654443341299)
  ·
    refine ⟨317239295831423481665011949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211492863887615654443341299 317239295831423481665011949)
    ·
      refine ⟨118964735936783805624379481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 317239295831423481665011949 118964735936783805624379481)
      ·
        refine ⟨89223551952587854218284611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118964735936783805624379481 89223551952587854218284611)
        ·
          refine ⟨133835327928881781327426917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89223551952587854218284611 133835327928881781327426917)
          ·
            refine ⟨25094123986665333998892547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 133835327928881781327426917 25094123986665333998892547)
            ·
              refine ⟨37641185979998000998338821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25094123986665333998892547 37641185979998000998338821)
              ·
                refine ⟨7057722371249625187188529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37641185979998000998338821 7057722371249625187188529)
                ·
                  refine ⟨5293291778437218890391397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7057722371249625187188529 5293291778437218890391397)
                  ·
                    refine ⟨992492208456978541948387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5293291778437218890391397 992492208456978541948387)
                    ·
                      rfl

theorem cell23_5798615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 4, 2, 4].length) (baseStart_5798615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5798615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5798615 prefixEnd_5798615 := by exact prefixLift 5798615
  have htrace : WordTrace (prefixWord ++ tailWord_5798615) baseStart_5798615 baseEnd_5798615 := by
    simpa [prefixWord, tailWord_5798615, baseEnd_5798615] using wordTrace_append hprefix tailTrace_5798615
  have hstable : (prefixWord ++ tailWord_5798615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5798615).length < 2 ^ (prefixWord ++ tailWord_5798615).sum := by decide
  have hdescent : baseEnd_5798615 < baseStart_5798615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5798615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5798616 : List Nat := [2, 1, 2, 2, 3, 4, 2, 2, 1, 1, 3]
def baseStart_5798616 : Nat := 118140960795 + 5798616 * 2 ^ 59
def prefixEnd_5798616 : Nat := 4983230072969 + 3 ^ 40 * 5798616 * 2
def baseEnd_5798616 : Nat := 2977477138851590121932657

theorem tailTrace_5798616 : CollatzResearch.WordTrace tailWord_5798616 prefixEnd_5798616 2977477138851590121932657 := by
  unfold tailWord_5798616
  simp only [CollatzResearch.WordTrace]
  refine ⟨105746450180306015807063851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140995266907074687742751801 105746450180306015807063851)
  ·
    refine ⟨158619675270459023710595777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105746450180306015807063851 158619675270459023710595777)
    ·
      refine ⟨118964756452844267782946833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158619675270459023710595777 118964756452844267782946833)
      ·
        refine ⟨89223567339633200837210125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118964756452844267782946833 89223567339633200837210125)
        ·
          refine ⟨33458837752362450313953797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89223567339633200837210125 33458837752362450313953797)
          ·
            refine ⟨6273532078567959433866337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33458837752362450313953797 6273532078567959433866337)
            ·
              refine ⟨4705149058925969575399753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6273532078567959433866337 4705149058925969575399753)
              ·
                refine ⟨3528861794194477181549815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4705149058925969575399753 3528861794194477181549815)
                ·
                  refine ⟨5293292691291715772324723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3528861794194477181549815 5293292691291715772324723)
                  ·
                    refine ⟨7939939036937573658487085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5293292691291715772324723 7939939036937573658487085)
                    ·
                      refine ⟨2977477138851590121932657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7939939036937573658487085 2977477138851590121932657)
                      ·
                        rfl

theorem cell23_5798616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 2, 1, 1, 3].length) (baseStart_5798616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5798616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5798616 prefixEnd_5798616 := by exact prefixLift 5798616
  have htrace : WordTrace (prefixWord ++ tailWord_5798616) baseStart_5798616 baseEnd_5798616 := by
    simpa [prefixWord, tailWord_5798616, baseEnd_5798616] using wordTrace_append hprefix tailTrace_5798616
  have hstable : (prefixWord ++ tailWord_5798616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5798616).length < 2 ^ (prefixWord ++ tailWord_5798616).sum := by decide
  have hdescent : baseEnd_5798616 < baseStart_5798616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5798616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5798618 : List Nat := [3, 1, 1, 2, 2, 2, 1, 2, 3, 2, 4]
def baseStart_5798618 : Nat := 118140960795 + 5798618 * 2 ^ 59
def prefixEnd_5798618 : Nat := 4983230072969 + 3 ^ 40 * 5798618 * 2
def baseEnd_5798618 : Nat := 2977478165812899114107647

theorem tailTrace_5798618 : CollatzResearch.WordTrace tailWord_5798618 prefixEnd_5798618 2977478165812899114107647 := by
  unfold tailWord_5798618
  simp only [CollatzResearch.WordTrace]
  refine ⟨52873243326651196488925127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140995315537736523970467005 52873243326651196488925127)
  ·
    refine ⟨79309864989976794733387691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52873243326651196488925127 79309864989976794733387691)
    ·
      refine ⟨118964797484965192100081537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79309864989976794733387691 118964797484965192100081537)
      ·
        refine ⟨89223598113723894075061153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118964797484965192100081537 89223598113723894075061153)
        ·
          refine ⟨66917698585292920556295865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89223598113723894075061153 66917698585292920556295865)
          ·
            refine ⟨50188273938969690417221899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66917698585292920556295865 50188273938969690417221899)
            ·
              refine ⟨75282410908454535625832849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50188273938969690417221899 75282410908454535625832849)
              ·
                refine ⟨56461808181340901719374637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75282410908454535625832849 56461808181340901719374637)
                ·
                  refine ⟨21173178068002838144765489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56461808181340901719374637 21173178068002838144765489)
                  ·
                    refine ⟨15879883551002128608574117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21173178068002838144765489 15879883551002128608574117)
                    ·
                      refine ⟨2977478165812899114107647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15879883551002128608574117 2977478165812899114107647)
                      ·
                        rfl

theorem cell23_5798618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_5798618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5798618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5798618 prefixEnd_5798618 := by exact prefixLift 5798618
  have htrace : WordTrace (prefixWord ++ tailWord_5798618) baseStart_5798618 baseEnd_5798618 := by
    simpa [prefixWord, tailWord_5798618, baseEnd_5798618] using wordTrace_append hprefix tailTrace_5798618
  have hstable : (prefixWord ++ tailWord_5798618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5798618).length < 2 ^ (prefixWord ++ tailWord_5798618).sum := by decide
  have hdescent : baseEnd_5798618 < baseStart_5798618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5798618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5798625 : List Nat := [1, 2, 3, 1, 4, 1, 1, 2, 3, 2, 3]
def baseStart_5798625 : Nat := 118140960795 + 5798625 * 2 ^ 59
def prefixEnd_5798625 : Nat := 4983230072969 + 3 ^ 40 * 5798625 * 2
def baseEnd_5798625 : Nat := 2977481760177480586720115

theorem tailTrace_5798625 : CollatzResearch.WordTrace tailWord_5798625 prefixEnd_5798625 2977481760177480586720115 := by
  unfold tailWord_5798625
  simp only [CollatzResearch.WordTrace]
  refine ⟨211493228617579426151205329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140995485745052950767470219 211493228617579426151205329)
  ·
    refine ⟨158619921463184569613403997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211493228617579426151205329 158619921463184569613403997)
    ·
      refine ⟨59482470548694213605026499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158619921463184569613403997 59482470548694213605026499)
      ·
        refine ⟨89223705823041320407539749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59482470548694213605026499 89223705823041320407539749)
        ·
          refine ⟨16729444841820247576413703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89223705823041320407539749 16729444841820247576413703)
          ·
            refine ⟨25094167262730371364620555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16729444841820247576413703 25094167262730371364620555)
            ·
              refine ⟨37641250894095557046930833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25094167262730371364620555 37641250894095557046930833)
              ·
                refine ⟨28230938170571667785198125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37641250894095557046930833 28230938170571667785198125)
                ·
                  refine ⟨10586601813964375419449297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28230938170571667785198125 10586601813964375419449297)
                  ·
                    refine ⟨7939951360473281564586973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10586601813964375419449297 7939951360473281564586973)
                    ·
                      refine ⟨2977481760177480586720115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7939951360473281564586973 2977481760177480586720115)
                      ·
                        rfl

theorem cell23_5798625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 3, 2, 3].length) (baseStart_5798625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5798625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5798625 prefixEnd_5798625 := by exact prefixLift 5798625
  have htrace : WordTrace (prefixWord ++ tailWord_5798625) baseStart_5798625 baseEnd_5798625 := by
    simpa [prefixWord, tailWord_5798625, baseEnd_5798625] using wordTrace_append hprefix tailTrace_5798625
  have hstable : (prefixWord ++ tailWord_5798625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5798625).length < 2 ^ (prefixWord ++ tailWord_5798625).sum := by decide
  have hdescent : baseEnd_5798625 < baseStart_5798625 := by decide
  rcases family_descends (prefixWord ++ tailWord_5798625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5798628 : List Nat := [2, 3, 1, 1, 1, 4, 3, 8]
def baseStart_5798628 : Nat := 118140960795 + 5798628 * 2 ^ 59
def prefixEnd_5798628 : Nat := 4983230072969 + 3 ^ 40 * 5798628 * 2
def baseEnd_5798628 : Nat := 110277159282201632406763

theorem tailTrace_5798628 : CollatzResearch.WordTrace tailWord_5798628 prefixEnd_5798628 110277159282201632406763 := by
  unfold tailWord_5798628
  simp only [CollatzResearch.WordTrace]
  refine ⟨105746669018284278831782269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140995558691045705109043025 105746669018284278831782269)
  ·
    refine ⟨39655000881856604561918351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105746669018284278831782269 39655000881856604561918351)
    ·
      refine ⟨59482501322784906842877527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39655000881856604561918351 59482501322784906842877527)
      ·
        refine ⟨89223751984177360264316291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59482501322784906842877527 89223751984177360264316291)
        ·
          refine ⟨133835627976266040396474437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89223751984177360264316291 133835627976266040396474437)
          ·
            refine ⟨25094180245549882574338957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 133835627976266040396474437 25094180245549882574338957)
            ·
              refine ⟨9410317592081205965377109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25094180245549882574338957 9410317592081205965377109)
              ·
                refine ⟨110277159282201632406763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9410317592081205965377109 110277159282201632406763)
                ·
                  rfl

theorem cell23_5798628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 8].length) (baseStart_5798628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5798628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5798628 prefixEnd_5798628 := by exact prefixLift 5798628
  have htrace : WordTrace (prefixWord ++ tailWord_5798628) baseStart_5798628 baseEnd_5798628 := by
    simpa [prefixWord, tailWord_5798628, baseEnd_5798628] using wordTrace_append hprefix tailTrace_5798628
  have hstable : (prefixWord ++ tailWord_5798628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5798628).length < 2 ^ (prefixWord ++ tailWord_5798628).sum := by decide
  have hdescent : baseEnd_5798628 < baseStart_5798628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5798628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5798655 : List Nat := [1, 1, 2, 2, 1, 3, 1, 4, 4, 1, 3]
def baseStart_5798655 : Nat := 118140960795 + 5798655 * 2 ^ 59
def prefixEnd_5798655 : Nat := 4983230072969 + 3 ^ 40 * 5798655 * 2
def baseEnd_5798655 : Nat := 2977497164597115469344977

theorem tailTrace_5798655 : CollatzResearch.WordTrace tailWord_5798655 prefixEnd_5798655 2977497164597115469344977 := by
  unfold tailWord_5798655
  simp only [CollatzResearch.WordTrace]
  refine ⟨211494322807470741274797419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140996215204980494183198279 211494322807470741274797419)
  ·
    refine ⟨317241484211206111912196129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211494322807470741274797419 317241484211206111912196129)
    ·
      refine ⟨237931113158404583934147097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317241484211206111912196129 237931113158404583934147097)
      ·
        refine ⟨178448334868803437950610323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237931113158404583934147097 178448334868803437950610323)
        ·
          refine ⟨267672502303205156925915485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178448334868803437950610323 267672502303205156925915485)
          ·
            refine ⟨100377188363701933847218307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 267672502303205156925915485 100377188363701933847218307)
            ·
              refine ⟨150565782545552900770827461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100377188363701933847218307 150565782545552900770827461)
              ·
                refine ⟨28231084227291168894530149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 150565782545552900770827461 28231084227291168894530149)
                ·
                  refine ⟨5293328292617094167724403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28231084227291168894530149 5293328292617094167724403)
                  ·
                    refine ⟨7939992438925641251586605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5293328292617094167724403 7939992438925641251586605)
                    ·
                      refine ⟨2977497164597115469344977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7939992438925641251586605 2977497164597115469344977)
                      ·
                        rfl

theorem cell23_5798655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 4, 1, 3].length) (baseStart_5798655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5798655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5798655 prefixEnd_5798655 := by exact prefixLift 5798655
  have htrace : WordTrace (prefixWord ++ tailWord_5798655) baseStart_5798655 baseEnd_5798655 := by
    simpa [prefixWord, tailWord_5798655, baseEnd_5798655] using wordTrace_append hprefix tailTrace_5798655
  have hstable : (prefixWord ++ tailWord_5798655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5798655).length < 2 ^ (prefixWord ++ tailWord_5798655).sum := by decide
  have hdescent : baseEnd_5798655 < baseStart_5798655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5798655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5798689 : List Nat := [1, 2, 3, 2, 1, 2, 5, 1, 2, 1, 3]
def baseStart_5798689 : Nat := 118140960795 + 5798689 * 2 ^ 59
def prefixEnd_5798689 : Nat := 4983230072969 + 3 ^ 40 * 5798689 * 2
def baseEnd_5798689 : Nat := 2977514622939368336319821

theorem tailTrace_5798689 : CollatzResearch.WordTrace tailWord_5798689 prefixEnd_5798689 2977514622939368336319821 := by
  unfold tailWord_5798689
  simp only [CollatzResearch.WordTrace]
  refine ⟨211495562889347565081535121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140997041926231710054356747 211495562889347565081535121)
  ·
    refine ⟨158621672167010673811151341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211495562889347565081535121 158621672167010673811151341)
    ·
      refine ⟨59483127062629002679181753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158621672167010673811151341 59483127062629002679181753)
      ·
        refine ⟨44612345296971752009386315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59483127062629002679181753 44612345296971752009386315)
        ·
          refine ⟨66918517945457628014079473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44612345296971752009386315 66918517945457628014079473)
          ·
            refine ⟨50188888459093221010559605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66918517945457628014079473 50188888459093221010559605)
            ·
              refine ⟨4705208293039989469739963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50188888459093221010559605 4705208293039989469739963)
              ·
                refine ⟨7057812439559984204609945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4705208293039989469739963 7057812439559984204609945)
                ·
                  refine ⟨5293359329669988153457459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7057812439559984204609945 5293359329669988153457459)
                  ·
                    refine ⟨7940038994504982230186189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5293359329669988153457459 7940038994504982230186189)
                    ·
                      refine ⟨2977514622939368336319821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7940038994504982230186189 2977514622939368336319821)
                      ·
                        rfl

theorem cell23_5798689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 1, 2, 1, 3].length) (baseStart_5798689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5798689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5798689 prefixEnd_5798689 := by exact prefixLift 5798689
  have htrace : WordTrace (prefixWord ++ tailWord_5798689) baseStart_5798689 baseEnd_5798689 := by
    simpa [prefixWord, tailWord_5798689, baseEnd_5798689] using wordTrace_append hprefix tailTrace_5798689
  have hstable : (prefixWord ++ tailWord_5798689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5798689).length < 2 ^ (prefixWord ++ tailWord_5798689).sum := by decide
  have hdescent : baseEnd_5798689 < baseStart_5798689 := by decide
  rcases family_descends (prefixWord ++ tailWord_5798689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5798712 : List Nat := [2, 1, 2, 1, 3, 2, 1, 1, 6, 2, 2]
def baseStart_5798712 : Nat := 118140960795 + 5798712 * 2 ^ 59
def prefixEnd_5798712 : Nat := 4983230072969 + 3 ^ 40 * 5798712 * 2
def baseEnd_5798712 : Nat := 2977526432994421746332215

theorem tailTrace_5798712 : CollatzResearch.WordTrace tailWord_5798712 prefixEnd_5798712 2977526432994421746332215 := by
  unfold tailWord_5798712
  simp only [CollatzResearch.WordTrace]
  refine ⟨105748200884132120004811195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140997601178842826673081593 105748200884132120004811195)
  ·
    refine ⟨158622301326198180007216793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105748200884132120004811195 158622301326198180007216793)
    ·
      refine ⟨118966725994648635005412595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158622301326198180007216793 118966725994648635005412595)
      ·
        refine ⟨178450088991972952508118893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118966725994648635005412595 178450088991972952508118893)
        ·
          refine ⟨66918783371989857190544585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178450088991972952508118893 66918783371989857190544585)
          ·
            refine ⟨50189087528992392892908439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66918783371989857190544585 50189087528992392892908439)
            ·
              refine ⟨75283631293488589339362659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50189087528992392892908439 75283631293488589339362659)
              ·
                refine ⟨112925446940232884009043989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75283631293488589339362659 112925446940232884009043989)
                ·
                  refine ⟨5293380325323416437923937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 112925446940232884009043989 5293380325323416437923937)
                  ·
                    refine ⟨3970035243992562328442953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5293380325323416437923937 3970035243992562328442953)
                    ·
                      refine ⟨2977526432994421746332215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3970035243992562328442953 2977526432994421746332215)
                      ·
                        rfl

theorem cell23_5798712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 6, 2, 2].length) (baseStart_5798712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5798712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5798712 prefixEnd_5798712 := by exact prefixLift 5798712
  have htrace : WordTrace (prefixWord ++ tailWord_5798712) baseStart_5798712 baseEnd_5798712 := by
    simpa [prefixWord, tailWord_5798712, baseEnd_5798712] using wordTrace_append hprefix tailTrace_5798712
  have hstable : (prefixWord ++ tailWord_5798712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5798712).length < 2 ^ (prefixWord ++ tailWord_5798712).sum := by decide
  have hdescent : baseEnd_5798712 < baseStart_5798712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5798712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5798728 : List Nat := [2, 1, 3, 1, 1, 3, 1, 1, 1, 2, 7]
def baseStart_5798728 : Nat := 118140960795 + 5798728 * 2 ^ 59
def prefixEnd_5798728 : Nat := 4983230072969 + 3 ^ 40 * 5798728 * 2
def baseEnd_5798728 : Nat := 2977534648684893683732141

theorem tailTrace_5798728 : CollatzResearch.WordTrace tailWord_5798728 prefixEnd_5798728 2977534648684893683732141 := by
  unfold tailWord_5798728
  simp only [CollatzResearch.WordTrace]
  refine ⟨105748492668103137371102419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140997990224137516494803225 105748492668103137371102419)
  ·
    refine ⟨158622739002154706056653629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105748492668103137371102419 158622739002154706056653629)
    ·
      refine ⟨59483527125808014771245111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158622739002154706056653629 59483527125808014771245111)
      ·
        refine ⟨89225290688712022156867667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59483527125808014771245111 89225290688712022156867667)
        ·
          refine ⟨133837936033068033235301501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89225290688712022156867667 133837936033068033235301501)
          ·
            refine ⟨50189226012400512463238063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133837936033068033235301501 50189226012400512463238063)
            ·
              refine ⟨75283839018600768694857095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50189226012400512463238063 75283839018600768694857095)
              ·
                refine ⟨112925758527901153042285643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75283839018600768694857095 112925758527901153042285643)
                ·
                  refine ⟨169388637791851729563428465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112925758527901153042285643 169388637791851729563428465)
                  ·
                    refine ⟨127041478343888797172571349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 169388637791851729563428465 127041478343888797172571349)
                    ·
                      refine ⟨2977534648684893683732141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 127041478343888797172571349 2977534648684893683732141)
                      ·
                        rfl

theorem cell23_5798728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_5798728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5798728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5798728 prefixEnd_5798728 := by exact prefixLift 5798728
  have htrace : WordTrace (prefixWord ++ tailWord_5798728) baseStart_5798728 baseEnd_5798728 := by
    simpa [prefixWord, tailWord_5798728, baseEnd_5798728] using wordTrace_append hprefix tailTrace_5798728
  have hstable : (prefixWord ++ tailWord_5798728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5798728).length < 2 ^ (prefixWord ++ tailWord_5798728).sum := by decide
  have hdescent : baseEnd_5798728 < baseStart_5798728 := by decide
  rcases family_descends (prefixWord ++ tailWord_5798728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5798746 : List Nat := [3, 1, 1, 2, 1, 4, 4, 1, 2, 2, 2]
def baseStart_5798746 : Nat := 118140960795 + 5798746 * 2 ^ 59
def prefixEnd_5798746 : Nat := 4983230072969 + 3 ^ 40 * 5798746 * 2
def baseEnd_5798746 : Nat := 2977543891336674613307059

theorem tailTrace_5798746 : CollatzResearch.WordTrace tailWord_5798746 prefixEnd_5798746 2977543891336674613307059 := by
  unfold tailWord_5798746
  simp only [CollatzResearch.WordTrace]
  refine ⟨52874410462535265954090023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140998427900094042544240061 52874410462535265954090023)
  ·
    refine ⟨79311615693802898931135035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52874410462535265954090023 79311615693802898931135035)
    ·
      refine ⟨118967423540704348396702553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79311615693802898931135035 118967423540704348396702553)
      ·
        refine ⟨89225567655528261297526915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118967423540704348396702553 89225567655528261297526915)
        ·
          refine ⟨133838351483292391946290373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89225567655528261297526915 133838351483292391946290373)
          ·
            refine ⟨25094690903117323489929445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 133838351483292391946290373 25094690903117323489929445)
            ·
              refine ⟨4705254544334498154361771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25094690903117323489929445 4705254544334498154361771)
              ·
                refine ⟨7057881816501747231542657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4705254544334498154361771 7057881816501747231542657)
                ·
                  refine ⟨5293411362376310423656993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7057881816501747231542657 5293411362376310423656993)
                  ·
                    refine ⟨3970058521782232817742745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5293411362376310423656993 3970058521782232817742745)
                    ·
                      refine ⟨2977543891336674613307059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3970058521782232817742745 2977543891336674613307059)
                      ·
                        rfl

theorem cell23_5798746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 1, 2, 2, 2].length) (baseStart_5798746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5798746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5798746 prefixEnd_5798746 := by exact prefixLift 5798746
  have htrace : WordTrace (prefixWord ++ tailWord_5798746) baseStart_5798746 baseEnd_5798746 := by
    simpa [prefixWord, tailWord_5798746, baseEnd_5798746] using wordTrace_append hprefix tailTrace_5798746
  have hstable : (prefixWord ++ tailWord_5798746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5798746).length < 2 ^ (prefixWord ++ tailWord_5798746).sum := by decide
  have hdescent : baseEnd_5798746 < baseStart_5798746 := by decide
  rcases family_descends (prefixWord ++ tailWord_5798746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5798836 : List Nat := [2, 5, 2, 1, 1, 1, 1, 2, 2, 4, 2]
def baseStart_5798836 : Nat := 118140960795 + 5798836 * 2 ^ 59
def prefixEnd_5798836 : Nat := 4983230072969 + 3 ^ 40 * 5798836 * 2
def baseEnd_5798836 : Nat := 2977590104595579261181645

theorem tailTrace_5798836 : CollatzResearch.WordTrace tailWord_5798836 prefixEnd_5798836 2977590104595579261181645 := by
  unfold tailWord_5798836
  simp only [CollatzResearch.WordTrace]
  refine ⟨105750462209907504593568181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141000616279876672791424241 105750462209907504593568181)
  ·
    refine ⟨9914105832178828555647017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 105750462209907504593568181 9914105832178828555647017)
    ·
      refine ⟨7435579374134121416735263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9914105832178828555647017 7435579374134121416735263)
      ·
        refine ⟨11153369061201182125102895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7435579374134121416735263 11153369061201182125102895)
        ·
          refine ⟨16730053591801773187654343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11153369061201182125102895 16730053591801773187654343)
          ·
            refine ⟨25095080387702659781481515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16730053591801773187654343 25095080387702659781481515)
            ·
              refine ⟨37642620581553989672222273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25095080387702659781481515 37642620581553989672222273)
              ·
                refine ⟨28231965436165492254166705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37642620581553989672222273 28231965436165492254166705)
                ·
                  refine ⟨21173974077124119190625029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28231965436165492254166705 21173974077124119190625029)
                  ·
                    refine ⟨3970120139460772348242193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21173974077124119190625029 3970120139460772348242193)
                    ·
                      refine ⟨2977590104595579261181645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3970120139460772348242193 2977590104595579261181645)
                      ·
                        rfl

theorem cell23_5798836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_5798836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5798836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5798836 prefixEnd_5798836 := by exact prefixLift 5798836
  have htrace : WordTrace (prefixWord ++ tailWord_5798836) baseStart_5798836 baseEnd_5798836 := by
    simpa [prefixWord, tailWord_5798836, baseEnd_5798836] using wordTrace_append hprefix tailTrace_5798836
  have hstable : (prefixWord ++ tailWord_5798836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5798836).length < 2 ^ (prefixWord ++ tailWord_5798836).sum := by decide
  have hdescent : baseEnd_5798836 < baseStart_5798836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5798836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5798855 : List Nat := [1, 1, 4, 1, 1, 2, 2, 1, 5, 5]
def baseStart_5798855 : Nat := 118140960795 + 5798855 * 2 ^ 59
def prefixEnd_5798855 : Nat := 4983230072969 + 3 ^ 40 * 5798855 * 2
def baseEnd_5798855 : Nat := 992533286909338228948019

theorem tailTrace_5798855 : CollatzResearch.WordTrace tailWord_5798855 prefixEnd_5798855 992533286909338228948019 := by
  unfold tailWord_5798855
  simp only [CollatzResearch.WordTrace]
  refine ⟨211501617406746175432078019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141001078271164116954718679 211501617406746175432078019)
  ·
    refine ⟨317252426110119263148117029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211501617406746175432078019 317252426110119263148117029)
    ·
      refine ⟨59484829895647361840271943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 317252426110119263148117029 59484829895647361840271943)
      ·
        refine ⟨89227244843471042760407915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59484829895647361840271943 89227244843471042760407915)
        ·
          refine ⟨133840867265206564140611873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89227244843471042760407915 133840867265206564140611873)
          ·
            refine ⟨100380650448904923105458905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133840867265206564140611873 100380650448904923105458905)
            ·
              refine ⟨75285487836678692329094179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100380650448904923105458905 75285487836678692329094179)
              ·
                refine ⟨112928231755018038493641269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75285487836678692329094179 112928231755018038493641269)
                ·
                  refine ⟨10587021727032941108778869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 112928231755018038493641269 10587021727032941108778869)
                  ·
                    refine ⟨992533286909338228948019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10587021727032941108778869 992533286909338228948019)
                    ·
                      rfl

theorem cell23_5798855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 5, 5].length) (baseStart_5798855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5798855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5798855 prefixEnd_5798855 := by exact prefixLift 5798855
  have htrace : WordTrace (prefixWord ++ tailWord_5798855) baseStart_5798855 baseEnd_5798855 := by
    simpa [prefixWord, tailWord_5798855, baseEnd_5798855] using wordTrace_append hprefix tailTrace_5798855
  have hstable : (prefixWord ++ tailWord_5798855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5798855).length < 2 ^ (prefixWord ++ tailWord_5798855).sum := by decide
  have hdescent : baseEnd_5798855 < baseStart_5798855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5798855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5798872 : List Nat := [2, 1, 2, 2, 2, 3, 1, 4, 1, 5]
def baseStart_5798872 : Nat := 118140960795 + 5798872 * 2 ^ 59
def prefixEnd_5798872 : Nat := 4983230072969 + 3 ^ 40 * 5798872 * 2
def baseEnd_5798872 : Nat := 992536196633047040110493

theorem tailTrace_5798872 : CollatzResearch.WordTrace tailWord_5798872 prefixEnd_5798872 992536196633047040110493 := by
  unfold tailWord_5798872
  simp only [CollatzResearch.WordTrace]
  refine ⟨105751118723842293667723435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141001491631789724890297913 105751118723842293667723435)
  ·
    refine ⟨158626678085763440501585153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105751118723842293667723435 158626678085763440501585153)
    ·
      refine ⟨118970008564322580376188865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158626678085763440501585153 118970008564322580376188865)
      ·
        refine ⟨89227506423241935282141649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118970008564322580376188865 89227506423241935282141649)
        ·
          refine ⟨66920629817431451461606237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89227506423241935282141649 66920629817431451461606237)
          ·
            refine ⟨25095236181536794298102339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66920629817431451461606237 25095236181536794298102339)
            ·
              refine ⟨37642854272305191447153509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25095236181536794298102339 37642854272305191447153509)
              ·
                refine ⟨7058035176057223396341283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37642854272305191447153509 7058035176057223396341283)
                ·
                  refine ⟨10587052764085835094511925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7058035176057223396341283 10587052764085835094511925)
                  ·
                    refine ⟨992536196633047040110493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10587052764085835094511925 992536196633047040110493)
                    ·
                      rfl

theorem cell23_5798872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 4, 1, 5].length) (baseStart_5798872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5798872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5798872 prefixEnd_5798872 := by exact prefixLift 5798872
  have htrace : WordTrace (prefixWord ++ tailWord_5798872) baseStart_5798872 baseEnd_5798872 := by
    simpa [prefixWord, tailWord_5798872, baseEnd_5798872] using wordTrace_append hprefix tailTrace_5798872
  have hstable : (prefixWord ++ tailWord_5798872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5798872).length < 2 ^ (prefixWord ++ tailWord_5798872).sum := by decide
  have hdescent : baseEnd_5798872 < baseStart_5798872 := by decide
  rcases family_descends (prefixWord ++ tailWord_5798872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5798905 : List Nat := [1, 2, 1, 3, 1, 3, 1, 1, 3, 1, 6]
def baseStart_5798905 : Nat := 118140960795 + 5798905 * 2 ^ 59
def prefixEnd_5798905 : Nat := 4983230072969 + 3 ^ 40 * 5798905 * 2
def baseEnd_5798905 : Nat := 2977625534760739491218827

theorem tailTrace_5798905 : CollatzResearch.WordTrace tailWord_5798905 prefixEnd_5798905 2977625534760739491218827 := by
  unfold tailWord_5798905
  simp only [CollatzResearch.WordTrace]
  refine ⟨211503441056565033971398169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141002294037710022647598779 211503441056565033971398169)
  ·
    refine ⟨158627580792423775478548627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211503441056565033971398169 158627580792423775478548627)
    ·
      refine ⟨237941371188635663217822941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158627580792423775478548627 237941371188635663217822941)
      ·
        refine ⟨89228014195738373706683603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 237941371188635663217822941 89228014195738373706683603)
        ·
          refine ⟨133842021293607560560025405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89228014195738373706683603 133842021293607560560025405)
          ·
            refine ⟨50190757985102835210009527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133842021293607560560025405 50190757985102835210009527)
            ·
              refine ⟨75286136977654252815014291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50190757985102835210009527 75286136977654252815014291)
              ·
                refine ⟨112929205466481379222521437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75286136977654252815014291 112929205466481379222521437)
                ·
                  refine ⟨42348452049930517208445539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112929205466481379222521437 42348452049930517208445539)
                  ·
                    refine ⟨63522678074895775812668309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42348452049930517208445539 63522678074895775812668309)
                    ·
                      refine ⟨2977625534760739491218827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63522678074895775812668309 2977625534760739491218827)
                      ·
                        rfl

theorem cell23_5798905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_5798905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5798905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5798905 prefixEnd_5798905 := by exact prefixLift 5798905
  have htrace : WordTrace (prefixWord ++ tailWord_5798905) baseStart_5798905 baseEnd_5798905 := by
    simpa [prefixWord, tailWord_5798905, baseEnd_5798905] using wordTrace_append hprefix tailTrace_5798905
  have hstable : (prefixWord ++ tailWord_5798905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5798905).length < 2 ^ (prefixWord ++ tailWord_5798905).sum := by decide
  have hdescent : baseEnd_5798905 < baseStart_5798905 := by decide
  rcases family_descends (prefixWord ++ tailWord_5798905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5798919 : List Nat := [1, 1, 4, 3, 1, 1, 3, 3, 2, 4]
def baseStart_5798919 : Nat := 118140960795 + 5798919 * 2 ^ 59
def prefixEnd_5798919 : Nat := 4983230072969 + 3 ^ 40 * 5798919 * 2
def baseEnd_5798919 : Nat := 992544241163300812147921

theorem tailTrace_5798919 : CollatzResearch.WordTrace tailWord_5798919 prefixEnd_5798919 992544241163300812147921 := by
  unfold tailWord_5798919
  simp only [CollatzResearch.WordTrace]
  refine ⟨211503951678514314362407811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141002634452342876241605207 211503951678514314362407811)
  ·
    refine ⟨317255927517771471543611717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211503951678514314362407811 317255927517771471543611717)
    ·
      refine ⟨59485486409582150914427197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 317255927517771471543611717 59485486409582150914427197)
      ·
        refine ⟨22307057403593306592910199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59485486409582150914427197 22307057403593306592910199)
        ·
          refine ⟨33460586105389959889365299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22307057403593306592910199 33460586105389959889365299)
          ·
            refine ⟨50190879158084939834047949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33460586105389959889365299 50190879158084939834047949)
            ·
              refine ⟨18821579684281852437767981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50190879158084939834047949 18821579684281852437767981)
              ·
                refine ⟨7058092381605694664162993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18821579684281852437767981 7058092381605694664162993)
                ·
                  refine ⟨5293569286204270998122245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7058092381605694664162993 5293569286204270998122245)
                  ·
                    refine ⟨992544241163300812147921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5293569286204270998122245 992544241163300812147921)
                    ·
                      rfl

theorem cell23_5798919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 3, 2, 4].length) (baseStart_5798919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5798919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5798919 prefixEnd_5798919 := by exact prefixLift 5798919
  have htrace : WordTrace (prefixWord ++ tailWord_5798919) baseStart_5798919 baseEnd_5798919 := by
    simpa [prefixWord, tailWord_5798919, baseEnd_5798919] using wordTrace_append hprefix tailTrace_5798919
  have hstable : (prefixWord ++ tailWord_5798919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5798919).length < 2 ^ (prefixWord ++ tailWord_5798919).sum := by decide
  have hdescent : baseEnd_5798919 < baseStart_5798919 := by decide
  rcases family_descends (prefixWord ++ tailWord_5798919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5798922 : List Nat := [3, 1, 2, 2, 3, 1, 2, 1, 1, 1, 6]
def baseStart_5798922 : Nat := 118140960795 + 5798922 * 2 ^ 59
def prefixEnd_5798922 : Nat := 4983230072969 + 3 ^ 40 * 5798922 * 2
def baseEnd_5798922 : Nat := 2977634263931865924706249

theorem tailTrace_5798922 : CollatzResearch.WordTrace tailWord_5798922 prefixEnd_5798922 2977634263931865924706249 := by
  unfold tailWord_5798922
  simp only [CollatzResearch.WordTrace]
  refine ⟨52876015274375861468691755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141002707398335630583178013 52876015274375861468691755)
  ·
    refine ⟨79314022911563792203037633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52876015274375861468691755 79314022911563792203037633)
    ·
      refine ⟨59485517183672844152278225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79314022911563792203037633 59485517183672844152278225)
      ·
        refine ⟨44614137887754633114208669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59485517183672844152278225 44614137887754633114208669)
        ·
          refine ⟨16730301707907987417828251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44614137887754633114208669 16730301707907987417828251)
          ·
            refine ⟨25095452561861981126742377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16730301707907987417828251 25095452561861981126742377)
            ·
              refine ⟨18821589421396485845056783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25095452561861981126742377 18821589421396485845056783)
              ·
                refine ⟨28232384132094728767585175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18821589421396485845056783 28232384132094728767585175)
                ·
                  refine ⟨42348576198142093151377763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28232384132094728767585175 42348576198142093151377763)
                  ·
                    refine ⟨63522864297213139727066645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42348576198142093151377763 63522864297213139727066645)
                    ·
                      refine ⟨2977634263931865924706249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63522864297213139727066645 2977634263931865924706249)
                      ·
                        rfl

theorem cell23_5798922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_5798922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5798922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5798922 prefixEnd_5798922 := by exact prefixLift 5798922
  have htrace : WordTrace (prefixWord ++ tailWord_5798922) baseStart_5798922 baseEnd_5798922 := by
    simpa [prefixWord, tailWord_5798922, baseEnd_5798922] using wordTrace_append hprefix tailTrace_5798922
  have hstable : (prefixWord ++ tailWord_5798922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5798922).length < 2 ^ (prefixWord ++ tailWord_5798922).sum := by decide
  have hdescent : baseEnd_5798922 < baseStart_5798922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5798922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5798926 : List Nat := [4, 1, 1, 2, 2, 4, 1, 2, 1, 1, 4]
def baseStart_5798926 : Nat := 118140960795 + 5798926 * 2 ^ 59
def prefixEnd_5798926 : Nat := 4983230072969 + 3 ^ 40 * 5798926 * 2
def baseEnd_5798926 : Nat := 2977636317854483909056231

theorem tailTrace_5798926 : CollatzResearch.WordTrace tailWord_5798926 prefixEnd_5798926 2977636317854483909056231 := by
  unfold tailWord_5798926
  simp only [CollatzResearch.WordTrace]
  refine ⟨26438025873686119319739079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141002804659659303038608421 26438025873686119319739079)
  ·
    refine ⟨39657038810529178979608619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26438025873686119319739079 39657038810529178979608619)
    ·
      refine ⟨59485558215793768469412929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39657038810529178979608619 59485558215793768469412929)
      ·
        refine ⟨44614168661845326352059697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59485558215793768469412929 44614168661845326352059697)
        ·
          refine ⟨33460626496383994764044773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44614168661845326352059697 33460626496383994764044773)
          ·
            refine ⟨6273867468071999018258395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33460626496383994764044773 6273867468071999018258395)
            ·
              refine ⟨9410801202107998527387593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6273867468071999018258395 9410801202107998527387593)
              ·
                refine ⟨7058100901580998895540695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9410801202107998527387593 7058100901580998895540695)
                ·
                  refine ⟨10587151352371498343311043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7058100901580998895540695 10587151352371498343311043)
                  ·
                    refine ⟨15880727028557247514966565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10587151352371498343311043 15880727028557247514966565)
                    ·
                      refine ⟨2977636317854483909056231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15880727028557247514966565 2977636317854483909056231)
                      ·
                        rfl

theorem cell23_5798926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_5798926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5798926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5798926 prefixEnd_5798926 := by exact prefixLift 5798926
  have htrace : WordTrace (prefixWord ++ tailWord_5798926) baseStart_5798926 baseEnd_5798926 := by
    simpa [prefixWord, tailWord_5798926, baseEnd_5798926] using wordTrace_append hprefix tailTrace_5798926
  have hstable : (prefixWord ++ tailWord_5798926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5798926).length < 2 ^ (prefixWord ++ tailWord_5798926).sum := by decide
  have hdescent : baseEnd_5798926 < baseStart_5798926 := by decide
  rcases family_descends (prefixWord ++ tailWord_5798926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5799002 : List Nat := [3, 1, 1, 2, 1, 1, 2, 2, 1, 6, 3]
def baseStart_5799002 : Nat := 118140960795 + 5799002 * 2 ^ 59
def prefixEnd_5799002 : Nat := 4983230072969 + 3 ^ 40 * 5799002 * 2
def baseEnd_5799002 : Nat := 2977675342384225611705881

theorem tailTrace_5799002 : CollatzResearch.WordTrace tailWord_5799002 prefixEnd_5799002 2977675342384225611705881 := by
  unfold tailWord_5799002
  simp only [CollatzResearch.WordTrace]
  refine ⟨52876744734303404884419815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141004652624809079691786173 52876744734303404884419815)
  ·
    refine ⟨79315117101455107326629723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52876744734303404884419815 79315117101455107326629723)
    ·
      refine ⟨118972675652182660989944585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79315117101455107326629723 118972675652182660989944585)
      ·
        refine ⟨89229506739136995742458439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118972675652182660989944585 89229506739136995742458439)
        ·
          refine ⟨133844260108705493613687659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89229506739136995742458439 133844260108705493613687659)
          ·
            refine ⟨200766390163058240420531489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133844260108705493613687659 200766390163058240420531489)
            ·
              refine ⟨150574792622293680315398617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200766390163058240420531489 150574792622293680315398617)
              ·
                refine ⟨112931094466720260236548963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150574792622293680315398617 112931094466720260236548963)
                ·
                  refine ⟨169396641700080390354823445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112931094466720260236548963 169396641700080390354823445)
                  ·
                    refine ⟨7940467579691268297882349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 169396641700080390354823445 7940467579691268297882349)
                    ·
                      refine ⟨2977675342384225611705881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7940467579691268297882349 2977675342384225611705881)
                      ·
                        rfl

theorem cell23_5799002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 1, 6, 3].length) (baseStart_5799002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5799002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5799002 prefixEnd_5799002 := by exact prefixLift 5799002
  have htrace : WordTrace (prefixWord ++ tailWord_5799002) baseStart_5799002 baseEnd_5799002 := by
    simpa [prefixWord, tailWord_5799002, baseEnd_5799002] using wordTrace_append hprefix tailTrace_5799002
  have hstable : (prefixWord ++ tailWord_5799002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5799002).length < 2 ^ (prefixWord ++ tailWord_5799002).sum := by decide
  have hdescent : baseEnd_5799002 < baseStart_5799002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5799002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5799010 : List Nat := [3, 3, 2, 2, 1, 3, 1, 2, 2, 1, 3]
def baseStart_5799010 : Nat := 118140960795 + 5799010 * 2 ^ 59
def prefixEnd_5799010 : Nat := 4983230072969 + 3 ^ 40 * 5799010 * 2
def baseEnd_5799010 : Nat := 2977679450229461580405845

theorem tailTrace_5799010 : CollatzResearch.WordTrace tailWord_5799010 prefixEnd_5799010 2977679450229461580405845 := by
  unfold tailWord_5799010
  simp only [CollatzResearch.WordTrace]
  refine ⟨52876817680296159225992621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141004847147456424602646989 52876817680296159225992621)
  ·
    refine ⟨19828806630111059709747233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52876817680296159225992621 19828806630111059709747233)
    ·
      refine ⟨14871604972583294782310425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19828806630111059709747233 14871604972583294782310425)
      ·
        refine ⟨11153703729437471086732819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14871604972583294782310425 11153703729437471086732819)
        ·
          refine ⟨16730555594156206630099229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11153703729437471086732819 16730555594156206630099229)
          ·
            refine ⟨6273958347808577486287211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16730555594156206630099229 6273958347808577486287211)
            ·
              refine ⟨9410937521712866229430817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6273958347808577486287211 9410937521712866229430817)
              ·
                refine ⟨7058203141284649672073113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9410937521712866229430817 7058203141284649672073113)
                ·
                  refine ⟨5293652355963487254054835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7058203141284649672073113 5293652355963487254054835)
                  ·
                    refine ⟨7940478533945230881082253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5293652355963487254054835 7940478533945230881082253)
                    ·
                      refine ⟨2977679450229461580405845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7940478533945230881082253 2977679450229461580405845)
                      ·
                        rfl

theorem cell23_5799010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_5799010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5799010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5799010 prefixEnd_5799010 := by exact prefixLift 5799010
  have htrace : WordTrace (prefixWord ++ tailWord_5799010) baseStart_5799010 baseEnd_5799010 := by
    simpa [prefixWord, tailWord_5799010, baseEnd_5799010] using wordTrace_append hprefix tailTrace_5799010
  have hstable : (prefixWord ++ tailWord_5799010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5799010).length < 2 ^ (prefixWord ++ tailWord_5799010).sum := by decide
  have hdescent : baseEnd_5799010 < baseStart_5799010 := by decide
  rcases family_descends (prefixWord ++ tailWord_5799010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5799033 : List Nat := [1, 2, 1, 3, 5, 2, 1, 1, 1, 4, 2]
def baseStart_5799033 : Nat := 118140960795 + 5799033 * 2 ^ 59
def prefixEnd_5799033 : Nat := 4983230072969 + 3 ^ 40 * 5799033 * 2
def baseEnd_5799033 : Nat := 2977691260284514990418239

theorem tailTrace_5799033 : CollatzResearch.WordTrace tailWord_5799033 prefixEnd_5799033 2977691260284514990418239 := by
  unfold tailWord_5799033
  simp only [CollatzResearch.WordTrace]
  refine ⟨211508109600101311832057753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141005406400067541221371835 211508109600101311832057753)
  ·
    refine ⟨158631082200075983874043315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211508109600101311832057753 158631082200075983874043315)
    ·
      refine ⟨237946623300113975811064973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158631082200075983874043315 237946623300113975811064973)
      ·
        refine ⟨89229983737542740929149365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 237946623300113975811064973 89229983737542740929149365)
        ·
          refine ⟨8365310975394631962107753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89229983737542740929149365 8365310975394631962107753)
          ·
            refine ⟨6273983231545973971580815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8365310975394631962107753 6273983231545973971580815)
            ·
              refine ⟨9410974847318960957371223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6273983231545973971580815 9410974847318960957371223)
              ·
                refine ⟨14116462270978441436056835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9410974847318960957371223 14116462270978441436056835)
                ·
                  refine ⟨21174693406467662154085253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14116462270978441436056835 21174693406467662154085253)
                  ·
                    refine ⟨3970255013712686653890985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21174693406467662154085253 3970255013712686653890985)
                    ·
                      refine ⟨2977691260284514990418239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3970255013712686653890985 2977691260284514990418239)
                      ·
                        rfl

theorem cell23_5799033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 4, 2].length) (baseStart_5799033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5799033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5799033 prefixEnd_5799033 := by exact prefixLift 5799033
  have htrace : WordTrace (prefixWord ++ tailWord_5799033) baseStart_5799033 baseEnd_5799033 := by
    simpa [prefixWord, tailWord_5799033, baseEnd_5799033] using wordTrace_append hprefix tailTrace_5799033
  have hstable : (prefixWord ++ tailWord_5799033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5799033).length < 2 ^ (prefixWord ++ tailWord_5799033).sum := by decide
  have hdescent : baseEnd_5799033 < baseStart_5799033 := by decide
  rcases family_descends (prefixWord ++ tailWord_5799033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5799052 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 6, 5]
def baseStart_5799052 : Nat := 118140960795 + 5799052 * 2 ^ 59
def prefixEnd_5799052 : Nat := 4983230072969 + 3 ^ 40 * 5799052 * 2
def baseEnd_5799052 : Nat := 992567005472316805360217

theorem tailTrace_5799052 : CollatzResearch.WordTrace tailWord_5799052 prefixEnd_5799052 992567005472316805360217 := by
  unfold tailWord_5799052
  simp only [CollatzResearch.WordTrace]
  refine ⟨105754401293516239038499705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141005868391354985384666273 105754401293516239038499705)
  ·
    refine ⟨79315800970137179278874779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105754401293516239038499705 79315800970137179278874779)
    ·
      refine ⟨118973701455205768918312169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79315800970137179278874779 118973701455205768918312169)
      ·
        refine ⟨89230276091404326688734127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118973701455205768918312169 89230276091404326688734127)
        ·
          refine ⟨133845414137106490033101191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89230276091404326688734127 133845414137106490033101191)
          ·
            refine ⟨200768121205659735049651787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133845414137106490033101191 200768121205659735049651787)
            ·
              refine ⟨301152181808489602574477681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200768121205659735049651787 301152181808489602574477681)
              ·
                refine ⟨225864136356367201930858261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 301152181808489602574477681 225864136356367201930858261)
                ·
                  refine ⟨10587381391704712590508981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 225864136356367201930858261 10587381391704712590508981)
                  ·
                    refine ⟨992567005472316805360217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10587381391704712590508981 992567005472316805360217)
                    ·
                      rfl

theorem cell23_5799052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 6, 5].length) (baseStart_5799052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5799052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5799052 prefixEnd_5799052 := by exact prefixLift 5799052
  have htrace : WordTrace (prefixWord ++ tailWord_5799052) baseStart_5799052 baseEnd_5799052 := by
    simpa [prefixWord, tailWord_5799052, baseEnd_5799052] using wordTrace_append hprefix tailTrace_5799052
  have hstable : (prefixWord ++ tailWord_5799052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5799052).length < 2 ^ (prefixWord ++ tailWord_5799052).sum := by decide
  have hdescent : baseEnd_5799052 < baseStart_5799052 := by decide
  rcases family_descends (prefixWord ++ tailWord_5799052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5799069 : List Nat := [1, 4, 2, 1, 1, 2, 3, 2, 2, 5]
def baseStart_5799069 : Nat := 118140960795 + 5799069 * 2 ^ 59
def prefixEnd_5799069 : Nat := 4983230072969 + 3 ^ 40 * 5799069 * 2
def baseEnd_5799069 : Nat := 992569915196025616522691

theorem tailTrace_5799069 : CollatzResearch.WordTrace tailWord_5799069 prefixEnd_5799069 992569915196025616522691 := by
  unfold tailWord_5799069
  simp only [CollatzResearch.WordTrace]
  refine ⟨211509422627970889980368261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141006281751980593320245507 211509422627970889980368261)
  ·
    refine ⟨39658016742744541871319049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 211509422627970889980368261 39658016742744541871319049)
    ·
      refine ⟨29743512557058406403489287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39658016742744541871319049 29743512557058406403489287)
      ·
        refine ⟨44615268835587609605233931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29743512557058406403489287 44615268835587609605233931)
        ·
          refine ⟨66922903253381414407850897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44615268835587609605233931 66922903253381414407850897)
          ·
            refine ⟨50192177440036060805888173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66922903253381414407850897 50192177440036060805888173)
            ·
              refine ⟨18822066540013522802208065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50192177440036060805888173 18822066540013522802208065)
              ·
                refine ⟨14116549905010142101656049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18822066540013522802208065 14116549905010142101656049)
                ·
                  refine ⟨10587412428757606576242037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14116549905010142101656049 10587412428757606576242037)
                  ·
                    refine ⟨992569915196025616522691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10587412428757606576242037 992569915196025616522691)
                    ·
                      rfl

theorem cell23_5799069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_5799069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5799069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5799069 prefixEnd_5799069 := by exact prefixLift 5799069
  have htrace : WordTrace (prefixWord ++ tailWord_5799069) baseStart_5799069 baseEnd_5799069 := by
    simpa [prefixWord, tailWord_5799069, baseEnd_5799069] using wordTrace_append hprefix tailTrace_5799069
  have hstable : (prefixWord ++ tailWord_5799069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5799069).length < 2 ^ (prefixWord ++ tailWord_5799069).sum := by decide
  have hdescent : baseEnd_5799069 < baseStart_5799069 := by decide
  rcases family_descends (prefixWord ++ tailWord_5799069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5799079 : List Nat := [1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 7]
def baseStart_5799079 : Nat := 118140960795 + 5799079 * 2 ^ 59
def prefixEnd_5799079 : Nat := 4983230072969 + 3 ^ 40 * 5799079 * 2
def baseEnd_5799079 : Nat := 2977714880394621810443027

theorem tailTrace_5799079 : CollatzResearch.WordTrace tailWord_5799079 prefixEnd_5799079 2977714880394621810443027 := by
  unfold tailWord_5799079
  simp only [CollatzResearch.WordTrace]
  refine ⟨211509787357934661688232291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141006524905289774458821527 211509787357934661688232291)
  ·
    refine ⟨317264681036901992532348437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211509787357934661688232291 317264681036901992532348437)
    ·
      refine ⟨14871781923604780899953833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 317264681036901992532348437 14871781923604780899953833)
      ·
        refine ⟨11153836442703585674965375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14871781923604780899953833 11153836442703585674965375)
        ·
          refine ⟨16730754664055378512448063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11153836442703585674965375 16730754664055378512448063)
          ·
            refine ⟨25096131996083067768672095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16730754664055378512448063 25096131996083067768672095)
            ·
              refine ⟨37644197994124601653008143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25096131996083067768672095 37644197994124601653008143)
              ·
                refine ⟨56466296991186902479512215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37644197994124601653008143 56466296991186902479512215)
                ·
                  refine ⟨84699445486780353719268323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56466296991186902479512215 84699445486780353719268323)
                  ·
                    refine ⟨127049168230170530578902485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 84699445486780353719268323 127049168230170530578902485)
                    ·
                      refine ⟨2977714880394621810443027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 127049168230170530578902485 2977714880394621810443027)
                      ·
                        rfl

theorem cell23_5799079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_5799079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5799079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5799079 prefixEnd_5799079 := by exact prefixLift 5799079
  have htrace : WordTrace (prefixWord ++ tailWord_5799079) baseStart_5799079 baseEnd_5799079 := by
    simpa [prefixWord, tailWord_5799079, baseEnd_5799079] using wordTrace_append hprefix tailTrace_5799079
  have hstable : (prefixWord ++ tailWord_5799079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5799079).length < 2 ^ (prefixWord ++ tailWord_5799079).sum := by decide
  have hdescent : baseEnd_5799079 < baseStart_5799079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5799079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5799112 : List Nat := [2, 1, 3, 1, 2, 1, 2, 1, 10]
def baseStart_5799112 : Nat := 118140960795 + 5799112 * 2 ^ 59
def prefixEnd_5799112 : Nat := 4983230072969 + 3 ^ 40 * 5799112 * 2
def baseEnd_5799112 : Nat := 330859091695135575703375

theorem tailTrace_5799112 : CollatzResearch.WordTrace tailWord_5799112 prefixEnd_5799112 330859091695135575703375 := by
  unfold tailWord_5799112
  simp only [CollatzResearch.WordTrace]
  refine ⟨105755495483407554162091795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141007327311210072216122393 105755495483407554162091795)
  ·
    refine ⟨158633243225111331243137693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105755495483407554162091795 158633243225111331243137693)
    ·
      refine ⟨59487466209416749216176635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158633243225111331243137693 59487466209416749216176635)
      ·
        refine ⟨89231199314125123824264953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59487466209416749216176635 89231199314125123824264953)
        ·
          refine ⟨66923399485593842868198715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89231199314125123824264953 66923399485593842868198715)
          ·
            refine ⟨100385099228390764302298073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66923399485593842868198715 100385099228390764302298073)
            ·
              refine ⟨75288824421293073226723555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100385099228390764302298073 75288824421293073226723555)
              ·
                refine ⟨112933236631939609840085333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75288824421293073226723555 112933236631939609840085333)
                ·
                  refine ⟨330859091695135575703375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 112933236631939609840085333 330859091695135575703375)
                  ·
                    rfl

theorem cell23_5799112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 10].length) (baseStart_5799112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5799112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5799112 prefixEnd_5799112 := by exact prefixLift 5799112
  have htrace : WordTrace (prefixWord ++ tailWord_5799112) baseStart_5799112 baseEnd_5799112 := by
    simpa [prefixWord, tailWord_5799112, baseEnd_5799112] using wordTrace_append hprefix tailTrace_5799112
  have hstable : (prefixWord ++ tailWord_5799112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5799112).length < 2 ^ (prefixWord ++ tailWord_5799112).sum := by decide
  have hdescent : baseEnd_5799112 < baseStart_5799112 := by decide
  rcases family_descends (prefixWord ++ tailWord_5799112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5799219 : List Nat := [1, 1, 1, 2, 5, 3, 1, 9]
def baseStart_5799219 : Nat := 118140960795 + 5799219 * 2 ^ 59
def prefixEnd_5799219 : Nat := 4983230072969 + 3 ^ 40 * 5799219 * 2
def baseEnd_5799219 : Nat := 110288398803194491210829

theorem tailTrace_5799219 : CollatzResearch.WordTrace tailWord_5799219 prefixEnd_5799219 110288398803194491210829 := by
  unfold tailWord_5799219
  simp only [CollatzResearch.WordTrace]
  refine ⟨211514893577427465598328711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141009929051618310398885807 211514893577427465598328711)
  ·
    refine ⟨317272340366141198397493067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211514893577427465598328711 317272340366141198397493067)
    ·
      refine ⟨475908510549211797596239601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317272340366141198397493067 475908510549211797596239601)
      ·
        refine ⟨356931382911908848197179701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 475908510549211797596239601 356931382911908848197179701)
        ·
          refine ⟨33462317147991454518485597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 356931382911908848197179701 33462317147991454518485597)
          ·
            refine ⟨12548368930496795444432099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33462317147991454518485597 12548368930496795444432099)
            ·
              refine ⟨18822553395745193166648149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12548368930496795444432099 18822553395745193166648149)
              ·
                refine ⟨110288398803194491210829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18822553395745193166648149 110288398803194491210829)
                ·
                  rfl

theorem cell23_5799219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 9].length) (baseStart_5799219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5799219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5799219 prefixEnd_5799219 := by exact prefixLift 5799219
  have htrace : WordTrace (prefixWord ++ tailWord_5799219) baseStart_5799219 baseEnd_5799219 := by
    simpa [prefixWord, tailWord_5799219, baseEnd_5799219] using wordTrace_append hprefix tailTrace_5799219
  have hstable : (prefixWord ++ tailWord_5799219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5799219).length < 2 ^ (prefixWord ++ tailWord_5799219).sum := by decide
  have hdescent : baseEnd_5799219 < baseStart_5799219 := by decide
  rcases family_descends (prefixWord ++ tailWord_5799219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5799233 : List Nat := [1, 2, 5, 2, 1, 2, 2, 1, 1, 1, 5]
def baseStart_5799233 : Nat := 118140960795 + 5799233 * 2 ^ 59
def prefixEnd_5799233 : Nat := 4983230072969 + 3 ^ 40 * 5799233 * 2
def baseEnd_5799233 : Nat := 2977793956415414207917319

theorem tailTrace_5799233 : CollatzResearch.WordTrace tailWord_5799233 prefixEnd_5799233 2977793956415414207917319 := by
  unfold tailWord_5799233
  simp only [CollatzResearch.WordTrace]
  refine ⟨211515404199376745989338353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141010269466251163992892235 211515404199376745989338353)
  ·
    refine ⟨158636553149532559492003765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211515404199376745989338353 158636553149532559492003765)
    ·
      refine ⟨14872176857768677452375353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 158636553149532559492003765 14872176857768677452375353)
      ·
        refine ⟨11154132643326508089281515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14872176857768677452375353 11154132643326508089281515)
        ·
          refine ⟨16731198964989762133922273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11154132643326508089281515 16731198964989762133922273)
          ·
            refine ⟨12548399223742321600441705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16731198964989762133922273 12548399223742321600441705)
            ·
              refine ⟨9411299417806741200331279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12548399223742321600441705 9411299417806741200331279)
              ·
                refine ⟨14116949126710111800496919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9411299417806741200331279 14116949126710111800496919)
                ·
                  refine ⟨21175423690065167700745379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14116949126710111800496919 21175423690065167700745379)
                  ·
                    refine ⟨31763135535097751551118069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21175423690065167700745379 31763135535097751551118069)
                    ·
                      refine ⟨2977793956415414207917319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31763135535097751551118069 2977793956415414207917319)
                      ·
                        rfl

theorem cell23_5799233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_5799233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5799233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5799233 prefixEnd_5799233 := by exact prefixLift 5799233
  have htrace : WordTrace (prefixWord ++ tailWord_5799233) baseStart_5799233 baseEnd_5799233 := by
    simpa [prefixWord, tailWord_5799233, baseEnd_5799233] using wordTrace_append hprefix tailTrace_5799233
  have hstable : (prefixWord ++ tailWord_5799233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5799233).length < 2 ^ (prefixWord ++ tailWord_5799233).sum := by decide
  have hdescent : baseEnd_5799233 < baseStart_5799233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5799233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5799236 : List Nat := [2, 3, 4, 1, 1, 1, 11]
def baseStart_5799236 : Nat := 118140960795 + 5799236 * 2 ^ 59
def prefixEnd_5799236 : Nat := 4983230072969 + 3 ^ 40 * 5799236 * 2
def baseEnd_5799236 : Nat := 36762907368609601187405

theorem tailTrace_5799236 : CollatzResearch.WordTrace tailWord_5799236 prefixEnd_5799236 36762907368609601187405 := by
  unfold tailWord_5799236
  simp only [CollatzResearch.WordTrace]
  refine ⟨105757756809182938750848781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141010342412243918334465041 105757756809182938750848781)
  ·
    refine ⟨39659158803443602031568293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105757756809182938750848781 39659158803443602031568293)
    ·
      refine ⟨7436092275645675380919055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39659158803443602031568293 7436092275645675380919055)
      ·
        refine ⟨11154138413468513071378583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7436092275645675380919055 11154138413468513071378583)
        ·
          refine ⟨16731207620202769607067875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11154138413468513071378583 16731207620202769607067875)
          ·
            refine ⟨25096811430304154410601813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16731207620202769607067875 25096811430304154410601813)
            ·
              refine ⟨36762907368609601187405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 25096811430304154410601813 36762907368609601187405)
              ·
                rfl

theorem cell23_5799236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 11].length) (baseStart_5799236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5799236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5799236 prefixEnd_5799236 := by exact prefixLift 5799236
  have htrace : WordTrace (prefixWord ++ tailWord_5799236) baseStart_5799236 baseEnd_5799236 := by
    simpa [prefixWord, tailWord_5799236, baseEnd_5799236] using wordTrace_append hprefix tailTrace_5799236
  have hstable : (prefixWord ++ tailWord_5799236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5799236).length < 2 ^ (prefixWord ++ tailWord_5799236).sum := by decide
  have hdescent : baseEnd_5799236 < baseStart_5799236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5799236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5799249 : List Nat := [1, 2, 2, 1, 4, 1, 2, 1, 2, 7]
def baseStart_5799249 : Nat := 118140960795 + 5799249 * 2 ^ 59
def prefixEnd_5799249 : Nat := 4983230072969 + 3 ^ 40 * 5799249 * 2
def baseEnd_5799249 : Nat := 992600724035295381772415

theorem tailTrace_5799249 : CollatzResearch.WordTrace tailWord_5799249 prefixEnd_5799249 992600724035295381772415 := by
  unfold tailWord_5799249
  simp only [CollatzResearch.WordTrace]
  refine ⟨211515987767318780721920801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141010658511545853814613867 211515987767318780721920801)
  ·
    refine ⟨158636990825489085541440601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211515987767318780721920801 158636990825489085541440601)
    ·
      refine ⟨118977743119116814156080451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158636990825489085541440601 118977743119116814156080451)
      ·
        refine ⟨178466614678675221234120677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118977743119116814156080451 178466614678675221234120677)
        ·
          refine ⟨33462490252251603981397627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 178466614678675221234120677 33462490252251603981397627)
          ·
            refine ⟨50193735378377405972096441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33462490252251603981397627 50193735378377405972096441)
            ·
              refine ⟨37645301533783054479072331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50193735378377405972096441 37645301533783054479072331)
              ·
                refine ⟨56467952300674581718608497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37645301533783054479072331 56467952300674581718608497)
                ·
                  refine ⟨42350964225505936288956373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56467952300674581718608497 42350964225505936288956373)
                  ·
                    refine ⟨992600724035295381772415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42350964225505936288956373 992600724035295381772415)
                    ·
                      rfl

theorem cell23_5799249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 7].length) (baseStart_5799249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5799249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5799249 prefixEnd_5799249 := by exact prefixLift 5799249
  have htrace : WordTrace (prefixWord ++ tailWord_5799249) baseStart_5799249 baseEnd_5799249 := by
    simpa [prefixWord, tailWord_5799249, baseEnd_5799249] using wordTrace_append hprefix tailTrace_5799249
  have hstable : (prefixWord ++ tailWord_5799249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5799249).length < 2 ^ (prefixWord ++ tailWord_5799249).sum := by decide
  have hdescent : baseEnd_5799249 < baseStart_5799249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5799249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5799273 : List Nat := [1, 2, 1, 1, 1, 3, 2, 6, 1, 3, 2]
def baseStart_5799273 : Nat := 118140960795 + 5799273 * 2 ^ 59
def prefixEnd_5799273 : Nat := 4983230072969 + 3 ^ 40 * 5799273 * 2
def baseEnd_5799273 : Nat := 2977814495641594051417135

theorem tailTrace_5799273 : CollatzResearch.WordTrace tailWord_5799273 prefixEnd_5799273 2977814495641594051417135 := by
  unfold tailWord_5799273
  simp only [CollatzResearch.WordTrace]
  refine ⟨211516863119231832820794473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141011242079487888547196315 211516863119231832820794473)
  ·
    refine ⟨158637647339423874615595855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211516863119231832820794473 158637647339423874615595855)
    ·
      refine ⟨237956471009135811923393783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158637647339423874615595855 237956471009135811923393783)
      ·
        refine ⟨356934706513703717885090675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237956471009135811923393783 356934706513703717885090675)
        ·
          refine ⟨535402059770555576827636013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356934706513703717885090675 535402059770555576827636013)
          ·
            refine ⟨200775772413958341310363505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 535402059770555576827636013 200775772413958341310363505)
            ·
              refine ⟨150581829310468755982772629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200775772413958341310363505 150581829310468755982772629)
              ·
                refine ⟨7058523248928222936692467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 150581829310468755982772629 7058523248928222936692467)
                ·
                  refine ⟨10587784873392334405038701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7058523248928222936692467 10587784873392334405038701)
                  ·
                    refine ⟨3970419327522125401889513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10587784873392334405038701 3970419327522125401889513)
                    ·
                      refine ⟨2977814495641594051417135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3970419327522125401889513 2977814495641594051417135)
                      ·
                        rfl

theorem cell23_5799273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 6, 1, 3, 2].length) (baseStart_5799273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5799273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5799273 prefixEnd_5799273 := by exact prefixLift 5799273
  have htrace : WordTrace (prefixWord ++ tailWord_5799273) baseStart_5799273 baseEnd_5799273 := by
    simpa [prefixWord, tailWord_5799273, baseEnd_5799273] using wordTrace_append hprefix tailTrace_5799273
  have hstable : (prefixWord ++ tailWord_5799273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5799273).length < 2 ^ (prefixWord ++ tailWord_5799273).sum := by decide
  have hdescent : baseEnd_5799273 < baseStart_5799273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5799273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5799297 : List Nat := [1, 2, 4, 3, 2, 1, 2, 2, 2, 1, 3]
def baseStart_5799297 : Nat := 118140960795 + 5799297 * 2 ^ 59
def prefixEnd_5799297 : Nat := 4983230072969 + 3 ^ 40 * 5799297 * 2
def baseEnd_5799297 : Nat := 2977826819177301957517025

theorem tailTrace_5799297 : CollatzResearch.WordTrace tailWord_5799297 prefixEnd_5799297 2977826819177301957517025 := by
  unfold tailWord_5799297
  simp only [CollatzResearch.WordTrace]
  refine ⟨211517738471144884919668145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141011825647429923279778763 211517738471144884919668145)
  ·
    refine ⟨158638303853358663689751109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211517738471144884919668145 158638303853358663689751109)
    ·
      refine ⟨29744681972504749441828333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158638303853358663689751109 29744681972504749441828333)
      ·
        refine ⟨11154255739689281040685625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29744681972504749441828333 11154255739689281040685625)
        ·
          refine ⟨8365691804766960780514219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11154255739689281040685625 8365691804766960780514219)
          ·
            refine ⟨12548537707150441170771329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8365691804766960780514219 12548537707150441170771329)
            ·
              refine ⟨9411403280362830878078497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12548537707150441170771329 9411403280362830878078497)
              ·
                refine ⟨7058552460272123158558873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9411403280362830878078497 7058552460272123158558873)
                ·
                  refine ⟨5293914345204092368919155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7058552460272123158558873 5293914345204092368919155)
                  ·
                    refine ⟨7940871517806138553378733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5293914345204092368919155 7940871517806138553378733)
                    ·
                      refine ⟨2977826819177301957517025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7940871517806138553378733 2977826819177301957517025)
                      ·
                        rfl

theorem cell23_5799297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_5799297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5799297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5799297 prefixEnd_5799297 := by exact prefixLift 5799297
  have htrace : WordTrace (prefixWord ++ tailWord_5799297) baseStart_5799297 baseEnd_5799297 := by
    simpa [prefixWord, tailWord_5799297, baseEnd_5799297] using wordTrace_append hprefix tailTrace_5799297
  have hstable : (prefixWord ++ tailWord_5799297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5799297).length < 2 ^ (prefixWord ++ tailWord_5799297).sum := by decide
  have hdescent : baseEnd_5799297 < baseStart_5799297 := by decide
  rcases family_descends (prefixWord ++ tailWord_5799297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5799298 : List Nat := [3, 4, 2, 1, 1, 3, 2, 2, 1, 2, 2]
def baseStart_5799298 : Nat := 118140960795 + 5799298 * 2 ^ 59
def prefixEnd_5799298 : Nat := 4983230072969 + 3 ^ 40 * 5799298 * 2
def baseEnd_5799298 : Nat := 2977827332657956453604521

theorem tailTrace_5799298 : CollatzResearch.WordTrace tailWord_5799298 prefixEnd_5799298 2977827332657956453604521 := by
  unfold tailWord_5799298
  simp only [CollatzResearch.WordTrace]
  refine ⟨52879443736035315522613637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141011849962760841393636365 52879443736035315522613637)
  ·
    refine ⟨9914895700506621660490057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52879443736035315522613637 9914895700506621660490057)
    ·
      refine ⟨7436171775379966245367543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9914895700506621660490057 7436171775379966245367543)
      ·
        refine ⟨11154257663069949368051315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7436171775379966245367543 11154257663069949368051315)
        ·
          refine ⟨16731386494604924052076973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11154257663069949368051315 16731386494604924052076973)
          ·
            refine ⟨6274269935476846519528865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16731386494604924052076973 6274269935476846519528865)
            ·
              refine ⟨4705702451607634889646649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6274269935476846519528865 4705702451607634889646649)
              ·
                refine ⟨3529276838705726167234987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4705702451607634889646649 3529276838705726167234987)
                ·
                  refine ⟨5293915258058589250852481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3529276838705726167234987 5293915258058589250852481)
                  ·
                    refine ⟨3970436443543941938139361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5293915258058589250852481 3970436443543941938139361)
                    ·
                      refine ⟨2977827332657956453604521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3970436443543941938139361 2977827332657956453604521)
                      ·
                        rfl

theorem cell23_5799298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_5799298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5799298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5799298 prefixEnd_5799298 := by exact prefixLift 5799298
  have htrace : WordTrace (prefixWord ++ tailWord_5799298) baseStart_5799298 baseEnd_5799298 := by
    simpa [prefixWord, tailWord_5799298, baseEnd_5799298] using wordTrace_append hprefix tailTrace_5799298
  have hstable : (prefixWord ++ tailWord_5799298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5799298).length < 2 ^ (prefixWord ++ tailWord_5799298).sum := by decide
  have hdescent : baseEnd_5799298 < baseStart_5799298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5799298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5799376 : List Nat := [2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 4]
def baseStart_5799376 : Nat := 118140960795 + 5799376 * 2 ^ 59
def prefixEnd_5799376 : Nat := 4983230072969 + 3 ^ 40 * 5799376 * 2
def baseEnd_5799376 : Nat := 2977867384149007148429161

theorem tailTrace_5799376 : CollatzResearch.WordTrace tailWord_5799376 prefixEnd_5799376 2977867384149007148429161 := by
  unfold tailWord_5799376
  simp only [CollatzResearch.WordTrace]
  refine ⟨105760309918929340705896991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141013746558572454274529321 105760309918929340705896991)
  ·
    refine ⟨158640464878394011058845487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105760309918929340705896991 158640464878394011058845487)
    ·
      refine ⟨237960697317591016588268231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158640464878394011058845487 237960697317591016588268231)
      ·
        refine ⟨356941045976386524882402347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237960697317591016588268231 356941045976386524882402347)
        ·
          refine ⟨535411568964579787323603521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356941045976386524882402347 535411568964579787323603521)
          ·
            refine ⟨401558676723434840492702641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 535411568964579787323603521 401558676723434840492702641)
            ·
              refine ⟨301169007542576130369526981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 401558676723434840492702641 301169007542576130369526981)
              ·
                refine ⟨56469188914233024444286309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 301169007542576130369526981 56469188914233024444286309)
                ·
                  refine ⟨10587972921418692083303683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56469188914233024444286309 10587972921418692083303683)
                  ·
                    refine ⟨15881959382128038124955525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10587972921418692083303683 15881959382128038124955525)
                    ·
                      refine ⟨2977867384149007148429161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15881959382128038124955525 2977867384149007148429161)
                      ·
                        rfl

theorem cell23_5799376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 4].length) (baseStart_5799376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5799376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5799376 prefixEnd_5799376 := by exact prefixLift 5799376
  have htrace : WordTrace (prefixWord ++ tailWord_5799376) baseStart_5799376 baseEnd_5799376 := by
    simpa [prefixWord, tailWord_5799376, baseEnd_5799376] using wordTrace_append hprefix tailTrace_5799376
  have hstable : (prefixWord ++ tailWord_5799376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5799376).length < 2 ^ (prefixWord ++ tailWord_5799376).sum := by decide
  have hdescent : baseEnd_5799376 < baseStart_5799376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5799376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5799410 : List Nat := [3, 2, 1, 4, 1, 2, 1, 2, 2, 1, 4]
def baseStart_5799410 : Nat := 118140960795 + 5799410 * 2 ^ 59
def prefixEnd_5799410 : Nat := 4983230072969 + 3 ^ 40 * 5799410 * 2
def baseEnd_5799410 : Nat := 2977884842491260015404005

theorem tailTrace_5799410 : CollatzResearch.WordTrace tailWord_5799410 prefixEnd_5799410 2977884842491260015404005 := by
  unfold tailWord_5799410
  simp only [CollatzResearch.WordTrace]
  refine ⟨52880464979933876304632921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141014573279823670145687789 52880464979933876304632921)
  ·
    refine ⟨39660348734950407228474691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52880464979933876304632921 39660348734950407228474691)
    ·
      refine ⟨59490523102425610842712037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39660348734950407228474691 59490523102425610842712037)
      ·
        refine ⟨11154473081704802033008507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59490523102425610842712037 11154473081704802033008507)
        ·
          refine ⟨16731709622557203049512761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11154473081704802033008507 16731709622557203049512761)
          ·
            refine ⟨12548782216917902287134571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16731709622557203049512761 12548782216917902287134571)
            ·
              refine ⟨18823173325376853430701857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12548782216917902287134571 18823173325376853430701857)
              ·
                refine ⟨14117379994032640073026393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18823173325376853430701857 14117379994032640073026393)
                ·
                  refine ⟨10588034995524480054769795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14117379994032640073026393 10588034995524480054769795)
                  ·
                    refine ⟨15882052493286720082154693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10588034995524480054769795 15882052493286720082154693)
                    ·
                      refine ⟨2977884842491260015404005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15882052493286720082154693 2977884842491260015404005)
                      ·
                        rfl

theorem cell23_5799410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_5799410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5799410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5799410 prefixEnd_5799410 := by exact prefixLift 5799410
  have htrace : WordTrace (prefixWord ++ tailWord_5799410) baseStart_5799410 baseEnd_5799410 := by
    simpa [prefixWord, tailWord_5799410, baseEnd_5799410] using wordTrace_append hprefix tailTrace_5799410
  have hstable : (prefixWord ++ tailWord_5799410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5799410).length < 2 ^ (prefixWord ++ tailWord_5799410).sum := by decide
  have hdescent : baseEnd_5799410 < baseStart_5799410 := by decide
  rcases family_descends (prefixWord ++ tailWord_5799410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5799416 : List Nat := [2, 1, 2, 1, 1, 5, 2, 1, 8]
def baseStart_5799416 : Nat := 118140960795 + 5799416 * 2 ^ 59
def prefixEnd_5799416 : Nat := 4983230072969 + 3 ^ 40 * 5799416 * 2
def baseEnd_5799416 : Nat := 330876435930576332436553

theorem tailTrace_5799416 : CollatzResearch.WordTrace tailWord_5799416 prefixEnd_5799416 330876435930576332436553 := by
  unfold tailWord_5799416
  simp only [CollatzResearch.WordTrace]
  refine ⟨105761039378856884121625051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141014719171809178828833401 105761039378856884121625051)
  ·
    refine ⟨158641559068285326182437577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105761039378856884121625051 158641559068285326182437577)
    ·
      refine ⟨118981169301213994636828183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158641559068285326182437577 118981169301213994636828183)
      ·
        refine ⟨178471753951820991955242275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118981169301213994636828183 178471753951820991955242275)
        ·
          refine ⟨267707630927731487932863413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178471753951820991955242275 267707630927731487932863413)
          ·
            refine ⟨25097590399474826993705945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 267707630927731487932863413 25097590399474826993705945)
            ·
              refine ⟨18823192799606120245279459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25097590399474826993705945 18823192799606120245279459)
              ·
                refine ⟨28234789199409180367919189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18823192799606120245279459 28234789199409180367919189)
                ·
                  refine ⟨330876435930576332436553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28234789199409180367919189 330876435930576332436553)
                  ·
                    rfl

theorem cell23_5799416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 8].length) (baseStart_5799416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5799416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5799416 prefixEnd_5799416 := by exact prefixLift 5799416
  have htrace : WordTrace (prefixWord ++ tailWord_5799416) baseStart_5799416 baseEnd_5799416 := by
    simpa [prefixWord, tailWord_5799416, baseEnd_5799416] using wordTrace_append hprefix tailTrace_5799416
  have hstable : (prefixWord ++ tailWord_5799416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5799416).length < 2 ^ (prefixWord ++ tailWord_5799416).sum := by decide
  have hdescent : baseEnd_5799416 < baseStart_5799416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5799416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5799420 : List Nat := [2, 2, 2, 1, 2, 1, 2, 6, 1, 4]
def baseStart_5799420 : Nat := 118140960795 + 5799420 * 2 ^ 59
def prefixEnd_5799420 : Nat := 4983230072969 + 3 ^ 40 * 5799420 * 2
def baseEnd_5799420 : Nat := 992629992432601658759653

theorem tailTrace_5799420 : CollatzResearch.WordTrace tailWord_5799420 prefixEnd_5799420 992629992432601658759653 := by
  unfold tailWord_5799420
  simp only [CollatzResearch.WordTrace]
  refine ⟨105761112324849638463197857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141014816433132851284263809 105761112324849638463197857)
  ·
    refine ⟨79320834243637228847398393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105761112324849638463197857 79320834243637228847398393)
    ·
      refine ⟨59490625682727921635548795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79320834243637228847398393 59490625682727921635548795)
      ·
        refine ⟨89235938524091882453323193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59490625682727921635548795 89235938524091882453323193)
        ·
          refine ⟨66926953893068911839992395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89235938524091882453323193 66926953893068911839992395)
          ·
            refine ⟨100390430839603367759988593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66926953893068911839992395 100390430839603367759988593)
            ·
              refine ⟨75292823129702525819991445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100390430839603367759988593 75292823129702525819991445)
              ·
                refine ⟨3529351084204805897812099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 75292823129702525819991445 3529351084204805897812099)
                ·
                  refine ⟨5294026626307208846718149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3529351084204805897812099 5294026626307208846718149)
                  ·
                    refine ⟨992629992432601658759653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5294026626307208846718149 992629992432601658759653)
                    ·
                      rfl

theorem cell23_5799420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 6, 1, 4].length) (baseStart_5799420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5799420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5799420 prefixEnd_5799420 := by exact prefixLift 5799420
  have htrace : WordTrace (prefixWord ++ tailWord_5799420) baseStart_5799420 baseEnd_5799420 := by
    simpa [prefixWord, tailWord_5799420, baseEnd_5799420] using wordTrace_append hprefix tailTrace_5799420
  have hstable : (prefixWord ++ tailWord_5799420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5799420).length < 2 ^ (prefixWord ++ tailWord_5799420).sum := by decide
  have hdescent : baseEnd_5799420 < baseStart_5799420 := by decide
  rcases family_descends (prefixWord ++ tailWord_5799420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5799493 : List Nat := [1, 3, 1, 1, 1, 4, 4, 1, 1, 6]
def baseStart_5799493 : Nat := 118140960795 + 5799493 * 2 ^ 59
def prefixEnd_5799493 : Nat := 4983230072969 + 3 ^ 40 * 5799493 * 2
def baseEnd_5799493 : Nat := 992642487128527730222041

theorem tailTrace_5799493 : CollatzResearch.WordTrace tailWord_5799493 prefixEnd_5799493 992642487128527730222041 := by
  unfold tailWord_5799493
  simp only [CollatzResearch.WordTrace]
  refine ⟨211524887178434810393803133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141016591452289873595868755 211524887178434810393803133)
  ·
    refine ⟨79321832691913053897676175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211524887178434810393803133 79321832691913053897676175)
    ·
      refine ⟨118982749037869580846514263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79321832691913053897676175 118982749037869580846514263)
      ·
        refine ⟨178474123556804371269771395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118982749037869580846514263 178474123556804371269771395)
        ·
          refine ⟨267711185335206556904657093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178474123556804371269771395 267711185335206556904657093)
          ·
            refine ⟨50195847250351229419623205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 267711185335206556904657093 50195847250351229419623205)
            ·
              refine ⟨9411721359440855516179351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50195847250351229419623205 9411721359440855516179351)
              ·
                refine ⟨14117582039161283274269027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9411721359440855516179351 14117582039161283274269027)
                ·
                  refine ⟨21176373058741924911403541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14117582039161283274269027 21176373058741924911403541)
                  ·
                    refine ⟨992642487128527730222041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21176373058741924911403541 992642487128527730222041)
                    ·
                      rfl

theorem cell23_5799493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 6].length) (baseStart_5799493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5799493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5799493 prefixEnd_5799493 := by exact prefixLift 5799493
  have htrace : WordTrace (prefixWord ++ tailWord_5799493) baseStart_5799493 baseEnd_5799493 := by
    simpa [prefixWord, tailWord_5799493, baseEnd_5799493] using wordTrace_append hprefix tailTrace_5799493
  have hstable : (prefixWord ++ tailWord_5799493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5799493).length < 2 ^ (prefixWord ++ tailWord_5799493).sum := by decide
  have hdescent : baseEnd_5799493 < baseStart_5799493 := by decide
  rcases family_descends (prefixWord ++ tailWord_5799493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5799603 : List Nat := [1, 1, 1, 2, 3, 3, 2, 1, 1, 4, 4]
def baseStart_5799603 : Nat := 118140960795 + 5799603 * 2 ^ 59
def prefixEnd_5799603 : Nat := 4983230072969 + 3 ^ 40 * 5799603 * 2
def baseEnd_5799603 : Nat := 2977983944257577760290617

theorem tailTrace_5799603 : CollatzResearch.WordTrace tailWord_5799603 prefixEnd_5799603 2977983944257577760290617 := by
  unfold tailWord_5799603
  simp only [CollatzResearch.WordTrace]
  refine ⟨211528899208036299180307463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141019266138690866120204975 211528899208036299180307463)
  ·
    refine ⟨317293348812054448770461195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211528899208036299180307463 317293348812054448770461195)
    ·
      refine ⟨475940023218081673155691793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317293348812054448770461195 475940023218081673155691793)
      ·
        refine ⟨356955017413561254866768845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 475940023218081673155691793 356955017413561254866768845)
        ·
          refine ⟨133858131530085470575038317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 356955017413561254866768845 133858131530085470575038317)
          ·
            refine ⟨50196799323782051465639369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133858131530085470575038317 50196799323782051465639369)
            ·
              refine ⟨37647599492836538599229527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50196799323782051465639369 37647599492836538599229527)
              ·
                refine ⟨56471399239254807898844291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37647599492836538599229527 56471399239254807898844291)
                ·
                  refine ⟨84707098858882211848266437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56471399239254807898844291 84707098858882211848266437)
                  ·
                    refine ⟨15882581036040414721549957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 84707098858882211848266437 15882581036040414721549957)
                    ·
                      refine ⟨2977983944257577760290617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15882581036040414721549957 2977983944257577760290617)
                      ·
                        rfl

theorem cell23_5799603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 4, 4].length) (baseStart_5799603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5799603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5799603 prefixEnd_5799603 := by exact prefixLift 5799603
  have htrace : WordTrace (prefixWord ++ tailWord_5799603) baseStart_5799603 baseEnd_5799603 := by
    simpa [prefixWord, tailWord_5799603, baseEnd_5799603] using wordTrace_append hprefix tailTrace_5799603
  have hstable : (prefixWord ++ tailWord_5799603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5799603).length < 2 ^ (prefixWord ++ tailWord_5799603).sum := by decide
  have hdescent : baseEnd_5799603 < baseStart_5799603 := by decide
  rcases family_descends (prefixWord ++ tailWord_5799603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5799613 : List Nat := [1, 4, 1, 2, 1, 2, 2, 1, 9]
def baseStart_5799613 : Nat := 118140960795 + 5799613 * 2 ^ 59
def prefixEnd_5799613 : Nat := 4983230072969 + 3 ^ 40 * 5799613 * 2
def baseEnd_5799613 : Nat := 330887675451569191240619

theorem tailTrace_5799613 : CollatzResearch.WordTrace tailWord_5799613 prefixEnd_5799613 330887675451569191240619 := by
  unfold tailWord_5799613
  simp only [CollatzResearch.WordTrace]
  refine ⟨211529263938000070888171493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141019509292000047258780995 211529263938000070888171493)
  ·
    refine ⟨39661736988375013291532155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 211529263938000070888171493 39661736988375013291532155)
    ·
      refine ⟨59492605482562519937298233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39661736988375013291532155 59492605482562519937298233)
      ·
        refine ⟨44619454111921889952973675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59492605482562519937298233 44619454111921889952973675)
        ·
          refine ⟨66929181167882834929460513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44619454111921889952973675 66929181167882834929460513)
          ·
            refine ⟨50196885875912126197095385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66929181167882834929460513 50196885875912126197095385)
            ·
              refine ⟨37647664406934094647821539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50196885875912126197095385 37647664406934094647821539)
              ·
                refine ⟨56471496610401141971732309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37647664406934094647821539 56471496610401141971732309)
                ·
                  refine ⟨330887675451569191240619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 56471496610401141971732309 330887675451569191240619)
                  ·
                    rfl

theorem cell23_5799613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 9].length) (baseStart_5799613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5799613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5799613 prefixEnd_5799613 := by exact prefixLift 5799613
  have htrace : WordTrace (prefixWord ++ tailWord_5799613) baseStart_5799613 baseEnd_5799613 := by
    simpa [prefixWord, tailWord_5799613, baseEnd_5799613] using wordTrace_append hprefix tailTrace_5799613
  have hstable : (prefixWord ++ tailWord_5799613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5799613).length < 2 ^ (prefixWord ++ tailWord_5799613).sum := by decide
  have hdescent : baseEnd_5799613 < baseStart_5799613 := by decide
  rcases family_descends (prefixWord ++ tailWord_5799613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5799640 : List Nat := [2, 1, 2, 2, 3, 1, 2, 2, 2, 3, 3]
def baseStart_5799640 : Nat := 118140960795 + 5799640 * 2 ^ 59
def prefixEnd_5799640 : Nat := 4983230072969 + 3 ^ 40 * 5799640 * 2
def baseEnd_5799640 : Nat := 2978002943041794115527947

theorem tailTrace_5799640 : CollatzResearch.WordTrace tailWord_5799640 prefixEnd_5799640 2978002943041794115527947 := by
  unfold tailWord_5799640
  simp only [CollatzResearch.WordTrace]
  refine ⟨105765124354451127249702187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141020165805934836332936249 105765124354451127249702187)
  ·
    refine ⟨158647686531676690874553281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105765124354451127249702187 158647686531676690874553281)
    ·
      refine ⟨118985764898757518155914961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158647686531676690874553281 118985764898757518155914961)
      ·
        refine ⟨89239323674068138616936221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118985764898757518155914961 89239323674068138616936221)
        ·
          refine ⟨33464746377775551981351083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89239323674068138616936221 33464746377775551981351083)
          ·
            refine ⟨50197119566663327972026625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33464746377775551981351083 50197119566663327972026625)
            ·
              refine ⟨37647839674997495979019969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50197119566663327972026625 37647839674997495979019969)
              ·
                refine ⟨28235879756248121984264977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37647839674997495979019969 28235879756248121984264977)
                ·
                  refine ⟨21176909817186091488198733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28235879756248121984264977 21176909817186091488198733)
                  ·
                    refine ⟨7941341181444784308074525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21176909817186091488198733 7941341181444784308074525)
                    ·
                      refine ⟨2978002943041794115527947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7941341181444784308074525 2978002943041794115527947)
                      ·
                        rfl

theorem cell23_5799640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 2, 3, 3].length) (baseStart_5799640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5799640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5799640 prefixEnd_5799640 := by exact prefixLift 5799640
  have htrace : WordTrace (prefixWord ++ tailWord_5799640) baseStart_5799640 baseEnd_5799640 := by
    simpa [prefixWord, tailWord_5799640, baseEnd_5799640] using wordTrace_append hprefix tailTrace_5799640
  have hstable : (prefixWord ++ tailWord_5799640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5799640).length < 2 ^ (prefixWord ++ tailWord_5799640).sum := by decide
  have hdescent : baseEnd_5799640 < baseStart_5799640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5799640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5799723 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 8]
def baseStart_5799723 : Nat := 118140960795 + 5799723 * 2 ^ 59
def prefixEnd_5799723 : Nat := 4983230072969 + 3 ^ 40 * 5799723 * 2
def baseEnd_5799723 : Nat := 2978045561936117290790065

theorem tailTrace_5799723 : CollatzResearch.WordTrace tailWord_5799723 prefixEnd_5799723 2978045561936117290790065 := by
  unfold tailWord_5799723
  simp only [CollatzResearch.WordTrace]
  refine ⟨211533275967601559674675823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141022183978401039783117215 211533275967601559674675823)
  ·
    refine ⟨317299913951402339512013735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211533275967601559674675823 317299913951402339512013735)
    ·
      refine ⟨475949870927103509268020603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317299913951402339512013735 475949870927103509268020603)
      ·
        refine ⟨713924806390655263902030905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475949870927103509268020603 713924806390655263902030905)
        ·
          refine ⟨535443604792991447926523179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 713924806390655263902030905 535443604792991447926523179)
          ·
            refine ⟨803165407189487171889784769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 535443604792991447926523179 803165407189487171889784769)
            ·
              refine ⟨602374055392115378917338577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 803165407189487171889784769 602374055392115378917338577)
              ·
                refine ⟨451780541544086534188003933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 602374055392115378917338577 451780541544086534188003933)
                ·
                  refine ⟨169417703079032450320501475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 451780541544086534188003933 169417703079032450320501475)
                  ·
                    refine ⟨254126554618548675480752213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 169417703079032450320501475 254126554618548675480752213)
                    ·
                      refine ⟨2978045561936117290790065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 254126554618548675480752213 2978045561936117290790065)
                      ·
                        rfl

theorem cell23_5799723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 8].length) (baseStart_5799723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5799723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5799723 prefixEnd_5799723 := by exact prefixLift 5799723
  have htrace : WordTrace (prefixWord ++ tailWord_5799723) baseStart_5799723 baseEnd_5799723 := by
    simpa [prefixWord, tailWord_5799723, baseEnd_5799723] using wordTrace_append hprefix tailTrace_5799723
  have hstable : (prefixWord ++ tailWord_5799723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5799723).length < 2 ^ (prefixWord ++ tailWord_5799723).sum := by decide
  have hdescent : baseEnd_5799723 < baseStart_5799723 := by decide
  rcases family_descends (prefixWord ++ tailWord_5799723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5799734 : List Nat := [5, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3]
def baseStart_5799734 : Nat := 118140960795 + 5799734 * 2 ^ 59
def prefixEnd_5799734 : Nat := 4983230072969 + 3 ^ 40 * 5799734 * 2
def baseEnd_5799734 : Nat := 2978051210223316747752515

theorem tailTrace_5799734 : CollatzResearch.WordTrace tailWord_5799734 prefixEnd_5799734 2978051210223316747752515 := by
  unfold tailWord_5799734
  simp only [CollatzResearch.WordTrace]
  refine ⟨13220854823160106784582891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141022451447041139035550837 13220854823160106784582891)
  ·
    refine ⟨19831282234740160176874337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13220854823160106784582891 19831282234740160176874337)
    ·
      refine ⟨14873461676055120132655753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19831282234740160176874337 14873461676055120132655753)
      ·
        refine ⟨11155096257041340099491815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14873461676055120132655753 11155096257041340099491815)
        ·
          refine ⟨16732644385562010149237723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11155096257041340099491815 16732644385562010149237723)
          ·
            refine ⟨25098966578343015223856585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16732644385562010149237723 25098966578343015223856585)
            ·
              refine ⟨18824224933757261417892439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25098966578343015223856585 18824224933757261417892439)
              ·
                refine ⟨28236337400635892126838659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18824224933757261417892439 28236337400635892126838659)
                ·
                  refine ⟨42354506100953838190257989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28236337400635892126838659 42354506100953838190257989)
                  ·
                    refine ⟨7941469893928844660673373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42354506100953838190257989 7941469893928844660673373)
                    ·
                      refine ⟨2978051210223316747752515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7941469893928844660673373 2978051210223316747752515)
                      ·
                        rfl

theorem cell23_5799734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_5799734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5799734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5799734 prefixEnd_5799734 := by exact prefixLift 5799734
  have htrace : WordTrace (prefixWord ++ tailWord_5799734) baseStart_5799734 baseEnd_5799734 := by
    simpa [prefixWord, tailWord_5799734, baseEnd_5799734] using wordTrace_append hprefix tailTrace_5799734
  have hstable : (prefixWord ++ tailWord_5799734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5799734).length < 2 ^ (prefixWord ++ tailWord_5799734).sum := by decide
  have hdescent : baseEnd_5799734 < baseStart_5799734 := by decide
  rcases family_descends (prefixWord ++ tailWord_5799734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5799741 : List Nat := [1, 4, 1, 4, 1, 1, 3, 3, 1, 4]
def baseStart_5799741 : Nat := 118140960795 + 5799741 * 2 ^ 59
def prefixEnd_5799741 : Nat := 4983230072969 + 3 ^ 40 * 5799741 * 2
def baseEnd_5799741 : Nat := 992684934862632740121661

theorem tailTrace_5799741 : CollatzResearch.WordTrace tailWord_5799741 prefixEnd_5799741 992684934862632740121661 := by
  unfold tailWord_5799741
  simp only [CollatzResearch.WordTrace]
  refine ⟨211533932481536348748831077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141022621654357565832554051 211533932481536348748831077)
  ·
    refine ⟨39662612340288065390405827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 211533932481536348748831077 39662612340288065390405827)
    ·
      refine ⟨59493918510432098085608741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39662612340288065390405827 59493918510432098085608741)
      ·
        refine ⟨11155109720706018391051639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59493918510432098085608741 11155109720706018391051639)
        ·
          refine ⟨16732664581059027586577459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11155109720706018391051639 16732664581059027586577459)
          ·
            refine ⟨25098996871588541379866189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16732664581059027586577459 25098996871588541379866189)
            ·
              refine ⟨9412123826845703017449821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25098996871588541379866189 9412123826845703017449821)
              ·
                refine ⟨3529546435067138631543683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9412123826845703017449821 3529546435067138631543683)
                ·
                  refine ⟨5294319652600707947315525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3529546435067138631543683 5294319652600707947315525)
                  ·
                    refine ⟨992684934862632740121661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5294319652600707947315525 992684934862632740121661)
                    ·
                      rfl

theorem cell23_5799741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 3, 1, 4].length) (baseStart_5799741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5799741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5799741 prefixEnd_5799741 := by exact prefixLift 5799741
  have htrace : WordTrace (prefixWord ++ tailWord_5799741) baseStart_5799741 baseEnd_5799741 := by
    simpa [prefixWord, tailWord_5799741, baseEnd_5799741] using wordTrace_append hprefix tailTrace_5799741
  have hstable : (prefixWord ++ tailWord_5799741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5799741).length < 2 ^ (prefixWord ++ tailWord_5799741).sum := by decide
  have hdescent : baseEnd_5799741 < baseStart_5799741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5799741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5799797 : List Nat := [1, 3, 4, 1, 1, 1, 3, 2, 1, 6]
def baseStart_5799797 : Nat := 118140960795 + 5799797 * 2 ^ 59
def prefixEnd_5799797 : Nat := 4983230072969 + 3 ^ 40 * 5799797 * 2
def baseEnd_5799797 : Nat := 992694519834850000421575

theorem tailTrace_5799797 : CollatzResearch.WordTrace tailWord_5799797 prefixEnd_5799797 992694519834850000421575 := by
  unfold tailWord_5799797
  simp only [CollatzResearch.WordTrace]
  refine ⟨211535974969333470312869645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141023983312888980208579763 211535974969333470312869645)
  ·
    refine ⟨79325990613500051367326117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211535974969333470312869645 79325990613500051367326117)
    ·
      refine ⟨14873623240031259631373647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79325990613500051367326117 14873623240031259631373647)
      ·
        refine ⟨22310434860046889447060471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14873623240031259631373647 22310434860046889447060471)
        ·
          refine ⟨33465652290070334170590707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22310434860046889447060471 33465652290070334170590707)
          ·
            refine ⟨50198478435105501255886061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33465652290070334170590707 50198478435105501255886061)
            ·
              refine ⟨18824429413164562970957273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50198478435105501255886061 18824429413164562970957273)
              ·
                refine ⟨14118322059873422228217955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18824429413164562970957273 14118322059873422228217955)
                ·
                  refine ⟨21177483089810133342326933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14118322059873422228217955 21177483089810133342326933)
                  ·
                    refine ⟨992694519834850000421575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21177483089810133342326933 992694519834850000421575)
                    ·
                      rfl

theorem cell23_5799797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_5799797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5799797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5799797 prefixEnd_5799797 := by exact prefixLift 5799797
  have htrace : WordTrace (prefixWord ++ tailWord_5799797) baseStart_5799797 baseEnd_5799797 := by
    simpa [prefixWord, tailWord_5799797, baseEnd_5799797] using wordTrace_append hprefix tailTrace_5799797
  have hstable : (prefixWord ++ tailWord_5799797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5799797).length < 2 ^ (prefixWord ++ tailWord_5799797).sum := by decide
  have hdescent : baseEnd_5799797 < baseStart_5799797 := by decide
  rcases family_descends (prefixWord ++ tailWord_5799797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5799815 : List Nat := [1, 1, 4, 2, 4, 2, 2, 2, 1, 1, 3]
def baseStart_5799815 : Nat := 118140960795 + 5799815 * 2 ^ 59
def prefixEnd_5799815 : Nat := 4983230072969 + 3 ^ 40 * 5799815 * 2
def baseEnd_5799815 : Nat := 2978092802156330930839643

theorem tailTrace_5799815 : CollatzResearch.WordTrace tailWord_5799815 prefixEnd_5799815 2978092802156330930839643 := by
  unfold tailWord_5799815
  simp only [CollatzResearch.WordTrace]
  refine ⟨211536631483268259387024899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141024420988845506258016599 211536631483268259387024899)
  ·
    refine ⟨317304947224902389080537349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211536631483268259387024899 317304947224902389080537349)
    ·
      refine ⟨59494677604669197952600753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 317304947224902389080537349 59494677604669197952600753)
      ·
        refine ⟨44621008203501898464450565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59494677604669197952600753 44621008203501898464450565)
        ·
          refine ⟨8366439038156605962084481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44621008203501898464450565 8366439038156605962084481)
          ·
            refine ⟨6274829278617454471563361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8366439038156605962084481 6274829278617454471563361)
            ·
              refine ⟨4706121958963090853672521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6274829278617454471563361 4706121958963090853672521)
              ·
                refine ⟨3529591469222318140254391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4706121958963090853672521 3529591469222318140254391)
                ·
                  refine ⟨5294387203833477210381587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3529591469222318140254391 5294387203833477210381587)
                  ·
                    refine ⟨7941580805750215815572381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5294387203833477210381587 7941580805750215815572381)
                    ·
                      refine ⟨2978092802156330930839643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7941580805750215815572381 2978092802156330930839643)
                      ·
                        rfl

theorem cell23_5799815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 2, 1, 1, 3].length) (baseStart_5799815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5799815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5799815 prefixEnd_5799815 := by exact prefixLift 5799815
  have htrace : WordTrace (prefixWord ++ tailWord_5799815) baseStart_5799815 baseEnd_5799815 := by
    simpa [prefixWord, tailWord_5799815, baseEnd_5799815] using wordTrace_append hprefix tailTrace_5799815
  have hstable : (prefixWord ++ tailWord_5799815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5799815).length < 2 ^ (prefixWord ++ tailWord_5799815).sum := by decide
  have hdescent : baseEnd_5799815 < baseStart_5799815 := by decide
  rcases family_descends (prefixWord ++ tailWord_5799815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5799834 : List Nat := [3, 1, 1, 4, 2, 2, 2, 1, 1, 2, 4]
def baseStart_5799834 : Nat := 118140960795 + 5799834 * 2 ^ 59
def prefixEnd_5799834 : Nat := 4983230072969 + 3 ^ 40 * 5799834 * 2
def baseEnd_5799834 : Nat := 2978102558288766356502055

theorem tailTrace_5799834 : CollatzResearch.WordTrace tailWord_5799834 prefixEnd_5799834 2978102558288766356502055 := by
  unfold tailWord_5799834
  simp only [CollatzResearch.WordTrace]
  refine ⟨52884331117549856407991639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141024882980132950421311037 52884331117549856407991639)
  ·
    refine ⟨79326496676324784611987459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52884331117549856407991639 79326496676324784611987459)
    ·
      refine ⟨118989745014487176917981189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79326496676324784611987459 118989745014487176917981189)
      ·
        refine ⟨22310577190216345672121473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118989745014487176917981189 22310577190216345672121473)
        ·
          refine ⟨16732932892662259254091105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22310577190216345672121473 16732932892662259254091105)
          ·
            refine ⟨12549699669496694440568329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16732932892662259254091105 12549699669496694440568329)
            ·
              refine ⟨9412274752122520830426247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12549699669496694440568329 9412274752122520830426247)
              ·
                refine ⟨14118412128183781245639371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9412274752122520830426247 14118412128183781245639371)
                ·
                  refine ⟨21177618192275671868459057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14118412128183781245639371 21177618192275671868459057)
                  ·
                    refine ⟨15883213644206753901344293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21177618192275671868459057 15883213644206753901344293)
                    ·
                      refine ⟨2978102558288766356502055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15883213644206753901344293 2978102558288766356502055)
                      ·
                        rfl

theorem cell23_5799834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_5799834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5799834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5799834 prefixEnd_5799834 := by exact prefixLift 5799834
  have htrace : WordTrace (prefixWord ++ tailWord_5799834) baseStart_5799834 baseEnd_5799834 := by
    simpa [prefixWord, tailWord_5799834, baseEnd_5799834] using wordTrace_append hprefix tailTrace_5799834
  have hstable : (prefixWord ++ tailWord_5799834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5799834).length < 2 ^ (prefixWord ++ tailWord_5799834).sum := by decide
  have hdescent : baseEnd_5799834 < baseStart_5799834 := by decide
  rcases family_descends (prefixWord ++ tailWord_5799834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5799840 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 4, 7]
def baseStart_5799840 : Nat := 118140960795 + 5799840 * 2 ^ 59
def prefixEnd_5799840 : Nat := 4983230072969 + 3 ^ 40 * 5799840 * 2
def baseEnd_5799840 : Nat := 992701879724231111009009

theorem tailTrace_5799840 : CollatzResearch.WordTrace tailWord_5799840 prefixEnd_5799840 992701879724231111009009 := by
  unfold tailWord_5799840
  simp only [CollatzResearch.WordTrace]
  refine ⟨105768771654088844328342487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141025028872118459104456649 105768771654088844328342487)
  ·
    refine ⟨158653157481133266492513731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105768771654088844328342487 158653157481133266492513731)
    ·
      refine ⟨237979736221699899738770597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158653157481133266492513731 237979736221699899738770597)
      ·
        refine ⟨44621200541568731201019487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 237979736221699899738770597 44621200541568731201019487)
        ·
          refine ⟨66931800812353096801529231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44621200541568731201019487 66931800812353096801529231)
          ·
            refine ⟨100397701218529645202293847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66931800812353096801529231 100397701218529645202293847)
            ·
              refine ⟨150596551827794467803440771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100397701218529645202293847 150596551827794467803440771)
              ·
                refine ⟨225894827741691701705161157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150596551827794467803440771 225894827741691701705161157)
                ·
                  refine ⟨42355280201567194069717717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 225894827741691701705161157 42355280201567194069717717)
                  ·
                    refine ⟨992701879724231111009009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42355280201567194069717717 992701879724231111009009)
                    ·
                      rfl

theorem cell23_5799840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 4, 7].length) (baseStart_5799840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5799840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5799840 prefixEnd_5799840 := by exact prefixLift 5799840
  have htrace : WordTrace (prefixWord ++ tailWord_5799840) baseStart_5799840 baseEnd_5799840 := by
    simpa [prefixWord, tailWord_5799840, baseEnd_5799840] using wordTrace_append hprefix tailTrace_5799840
  have hstable : (prefixWord ++ tailWord_5799840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5799840).length < 2 ^ (prefixWord ++ tailWord_5799840).sum := by decide
  have hdescent : baseEnd_5799840 < baseStart_5799840 := by decide
  rcases family_descends (prefixWord ++ tailWord_5799840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5799898 : List Nat := [3, 1, 1, 2, 5, 1, 2, 2, 1, 3, 2]
def baseStart_5799898 : Nat := 118140960795 + 5799898 * 2 ^ 59
def prefixEnd_5799898 : Nat := 4983230072969 + 3 ^ 40 * 5799898 * 2
def baseEnd_5799898 : Nat := 2978135421050654106101761

theorem tailTrace_5799898 : CollatzResearch.WordTrace tailWord_5799898 prefixEnd_5799898 2978135421050654106101761 := by
  unfold tailWord_5799898
  simp only [CollatzResearch.WordTrace]
  refine ⟨52884914685491891140574087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141026439161311709708197565 52884914685491891140574087)
  ·
    refine ⟨79327372028237836710861131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52884914685491891140574087 79327372028237836710861131)
    ·
      refine ⟨118991058042356755066291697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79327372028237836710861131 118991058042356755066291697)
      ·
        refine ⟨89243293531767566299718773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118991058042356755066291697 89243293531767566299718773)
        ·
          refine ⟨8366558768603209340598635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89243293531767566299718773 8366558768603209340598635)
          ·
            refine ⟨12549838152904814010897953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8366558768603209340598635 12549838152904814010897953)
            ·
              refine ⟨9412378614678610508173465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12549838152904814010897953 9412378614678610508173465)
              ·
                refine ⟨7059283961008957881130099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9412378614678610508173465 7059283961008957881130099)
                ·
                  refine ⟨10588925941513436821695149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7059283961008957881130099 10588925941513436821695149)
                  ·
                    refine ⟨3970847228067538808135681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10588925941513436821695149 3970847228067538808135681)
                    ·
                      refine ⟨2978135421050654106101761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3970847228067538808135681 2978135421050654106101761)
                      ·
                        rfl

theorem cell23_5799898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 2, 1, 3, 2].length) (baseStart_5799898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5799898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5799898 prefixEnd_5799898 := by exact prefixLift 5799898
  have htrace : WordTrace (prefixWord ++ tailWord_5799898) baseStart_5799898 baseEnd_5799898 := by
    simpa [prefixWord, tailWord_5799898, baseEnd_5799898] using wordTrace_append hprefix tailTrace_5799898
  have hstable : (prefixWord ++ tailWord_5799898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5799898).length < 2 ^ (prefixWord ++ tailWord_5799898).sum := by decide
  have hdescent : baseEnd_5799898 < baseStart_5799898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5799898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5799947 : List Nat := [1, 1, 1, 1, 6, 1, 1, 2, 4, 5]
def baseStart_5799947 : Nat := 118140960795 + 5799947 * 2 ^ 59
def prefixEnd_5799947 : Nat := 4983230072969 + 3 ^ 40 * 5799947 * 2
def baseEnd_5799947 : Nat := 992720193867574804796345

theorem tailTrace_5799947 : CollatzResearch.WordTrace tailWord_5799947 prefixEnd_5799947 992720193867574804796345 := by
  unfold tailWord_5799947
  simp only [CollatzResearch.WordTrace]
  refine ⟨211541445918790045930830095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141027630612526697287220063 211541445918790045930830095)
  ·
    refine ⟨317312168878185068896245143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211541445918790045930830095 317312168878185068896245143)
    ·
      refine ⟨475968253317277603344367715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317312168878185068896245143 475968253317277603344367715)
      ·
        refine ⟨713952379975916405016551573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475968253317277603344367715 713952379975916405016551573)
        ·
          refine ⟨33466517811371081485150855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 713952379975916405016551573 33466517811371081485150855)
          ·
            refine ⟨50199776717056622227726283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33466517811371081485150855 50199776717056622227726283)
            ·
              refine ⟨75299665075584933341589425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50199776717056622227726283 75299665075584933341589425)
              ·
                refine ⟨56474748806688700006192069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75299665075584933341589425 56474748806688700006192069)
                ·
                  refine ⟨10589015401254131251161013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56474748806688700006192069 10589015401254131251161013)
                  ·
                    refine ⟨992720193867574804796345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10589015401254131251161013 992720193867574804796345)
                    ·
                      rfl

theorem cell23_5799947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 4, 5].length) (baseStart_5799947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5799947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5799947 prefixEnd_5799947 := by exact prefixLift 5799947
  have htrace : WordTrace (prefixWord ++ tailWord_5799947) baseStart_5799947 baseEnd_5799947 := by
    simpa [prefixWord, tailWord_5799947, baseEnd_5799947] using wordTrace_append hprefix tailTrace_5799947
  have hstable : (prefixWord ++ tailWord_5799947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5799947).length < 2 ^ (prefixWord ++ tailWord_5799947).sum := by decide
  have hdescent : baseEnd_5799947 < baseStart_5799947 := by decide
  rcases family_descends (prefixWord ++ tailWord_5799947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5799949 : List Nat := [1, 7, 1, 2, 1, 2, 1, 2, 1, 3, 2]
def baseStart_5799949 : Nat := 118140960795 + 5799949 * 2 ^ 59
def prefixEnd_5799949 : Nat := 4983230072969 + 3 ^ 40 * 5799949 * 2
def baseEnd_5799949 : Nat := 2978161608564033406564027

theorem tailTrace_5799949 : CollatzResearch.WordTrace tailWord_5799949 prefixEnd_5799949 2978161608564033406564027 := by
  unfold tailWord_5799949
  simp only [CollatzResearch.WordTrace]
  refine ⟨211541518864782800272402901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141027679243188533514935267 211541518864782800272402901)
  ·
    refine ⟨4958004348393346881384443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 211541518864782800272402901 4958004348393346881384443)
    ·
      refine ⟨7437006522590020322076665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4958004348393346881384443 7437006522590020322076665)
      ·
        refine ⟨5577754891942515241557499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7437006522590020322076665 5577754891942515241557499)
        ·
          refine ⟨8366632337913772862336249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5577754891942515241557499 8366632337913772862336249)
          ·
            refine ⟨6274974253435329646752187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8366632337913772862336249 6274974253435329646752187)
            ·
              refine ⟨9412461380152994470128281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6274974253435329646752187 9412461380152994470128281)
              ·
                refine ⟨7059346035114745852596211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9412461380152994470128281 7059346035114745852596211)
                ·
                  refine ⟨10589019052672118778894317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7059346035114745852596211 10589019052672118778894317)
                  ·
                    refine ⟨3970882144752044542085369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10589019052672118778894317 3970882144752044542085369)
                    ·
                      refine ⟨2978161608564033406564027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3970882144752044542085369 2978161608564033406564027)
                      ·
                        rfl

theorem cell23_5799949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_5799949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5799949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5799949 prefixEnd_5799949 := by exact prefixLift 5799949
  have htrace : WordTrace (prefixWord ++ tailWord_5799949) baseStart_5799949 baseEnd_5799949 := by
    simpa [prefixWord, tailWord_5799949, baseEnd_5799949] using wordTrace_append hprefix tailTrace_5799949
  have hstable : (prefixWord ++ tailWord_5799949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5799949).length < 2 ^ (prefixWord ++ tailWord_5799949).sum := by decide
  have hdescent : baseEnd_5799949 < baseStart_5799949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5799949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5799964 : List Nat := [2, 2, 3, 1, 3, 1, 1, 3, 2, 5]
def baseStart_5799964 : Nat := 118140960795 + 5799964 * 2 ^ 59
def prefixEnd_5799964 : Nat := 4983230072969 + 3 ^ 40 * 5799964 * 2
def baseEnd_5799964 : Nat := 992723103591283615958819

theorem tailTrace_5799964 : CollatzResearch.WordTrace tailWord_5799964 prefixEnd_5799964 992723103591283615958819 := by
  unfold tailWord_5799964
  simp only [CollatzResearch.WordTrace]
  refine ⟨105771032979864228917099473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141028043973152305222799297 105771032979864228917099473)
  ·
    refine ⟨79328274734898171687824605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105771032979864228917099473 79328274734898171687824605)
    ·
      refine ⟨29748103025586814382934227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79328274734898171687824605 29748103025586814382934227)
      ·
        refine ⟨44622154538380221574401341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29748103025586814382934227 44622154538380221574401341)
        ·
          refine ⟨16733307951892583090400503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44622154538380221574401341 16733307951892583090400503)
          ·
            refine ⟨25099961927838874635600755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16733307951892583090400503 25099961927838874635600755)
            ·
              refine ⟨37649942891758311953401133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25099961927838874635600755 37649942891758311953401133)
              ·
                refine ⟨14118728584409366982525425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37649942891758311953401133 14118728584409366982525425)
                ·
                  refine ⟨10589046438307025236894069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14118728584409366982525425 10589046438307025236894069)
                  ·
                    refine ⟨992723103591283615958819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10589046438307025236894069 992723103591283615958819)
                    ·
                      rfl

theorem cell23_5799964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_5799964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5799964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5799964 prefixEnd_5799964 := by exact prefixLift 5799964
  have htrace : WordTrace (prefixWord ++ tailWord_5799964) baseStart_5799964 baseEnd_5799964 := by
    simpa [prefixWord, tailWord_5799964, baseEnd_5799964] using wordTrace_append hprefix tailTrace_5799964
  have hstable : (prefixWord ++ tailWord_5799964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5799964).length < 2 ^ (prefixWord ++ tailWord_5799964).sum := by decide
  have hdescent : baseEnd_5799964 < baseStart_5799964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5799964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5799984 : List Nat := [2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 4]
def baseStart_5799984 : Nat := 118140960795 + 5799984 * 2 ^ 59
def prefixEnd_5799984 : Nat := 4983230072969 + 3 ^ 40 * 5799984 * 2
def baseEnd_5799984 : Nat := 2978179580386940769626365

theorem tailTrace_5799984 : CollatzResearch.WordTrace tailWord_5799984 prefixEnd_5799984 2978179580386940769626365 := by
  unfold tailWord_5799984
  simp only [CollatzResearch.WordTrace]
  refine ⟨105771397709828000624963503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141028530279770667499951337 105771397709828000624963503)
  ·
    refine ⟨158657096564742000937445255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105771397709828000624963503 158657096564742000937445255)
    ·
      refine ⟨237985644847113001406167883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158657096564742000937445255 237985644847113001406167883)
      ·
        refine ⟨356978467270669502109251825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237985644847113001406167883 356978467270669502109251825)
        ·
          refine ⟨267733850453002126581938869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 356978467270669502109251825 267733850453002126581938869)
          ·
            refine ⟨25100048479968949367056769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 267733850453002126581938869 25100048479968949367056769)
            ·
              refine ⟨18825036359976712025292577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25100048479968949367056769 18825036359976712025292577)
              ·
                refine ⟨14118777269982534018969433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18825036359976712025292577 14118777269982534018969433)
                ·
                  refine ⟨10589082952486900514227075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14118777269982534018969433 10589082952486900514227075)
                  ·
                    refine ⟨15883624428730350771340613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10589082952486900514227075 15883624428730350771340613)
                    ·
                      refine ⟨2978179580386940769626365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15883624428730350771340613 2978179580386940769626365)
                      ·
                        rfl

theorem cell23_5799984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 4].length) (baseStart_5799984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5799984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5799984 prefixEnd_5799984 := by exact prefixLift 5799984
  have htrace : WordTrace (prefixWord ++ tailWord_5799984) baseStart_5799984 baseEnd_5799984 := by
    simpa [prefixWord, tailWord_5799984, baseEnd_5799984] using wordTrace_append hprefix tailTrace_5799984
  have hstable : (prefixWord ++ tailWord_5799984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5799984).length < 2 ^ (prefixWord ++ tailWord_5799984).sum := by decide
  have hdescent : baseEnd_5799984 < baseStart_5799984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5799984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5799994 : List Nat := [3, 1, 1, 1, 3, 1, 1, 5, 3, 4]
def baseStart_5799994 : Nat := 118140960795 + 5799994 * 2 ^ 59
def prefixEnd_5799994 : Nat := 4983230072969 + 3 ^ 40 * 5799994 * 2
def baseEnd_5799994 : Nat := 992728238397828576833773

theorem tailTrace_5799994 : CollatzResearch.WordTrace tailWord_5799994 prefixEnd_5799994 992728238397828576833773 := by
  unfold tailWord_5799994
  simp only [CollatzResearch.WordTrace]
  refine ⟨52885790037404943239447759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141028773433079848638527357 52885790037404943239447759)
  ·
    refine ⟨79328685056107414859171639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52885790037404943239447759 79328685056107414859171639)
    ·
      refine ⟨118993027584161122288757459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79328685056107414859171639 118993027584161122288757459)
      ·
        refine ⟨178489541376241683433136189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118993027584161122288757459 178489541376241683433136189)
        ·
          refine ⟨66933578016090631287426071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178489541376241683433136189 66933578016090631287426071)
          ·
            refine ⟨100400367024135946931139107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66933578016090631287426071 100400367024135946931139107)
            ·
              refine ⟨150600550536203920396708661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100400367024135946931139107 150600550536203920396708661)
              ·
                refine ⟨14118801612769117537191437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 150600550536203920396708661 14118801612769117537191437)
                ·
                  refine ⟨5294550604788419076446789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14118801612769117537191437 5294550604788419076446789)
                  ·
                    refine ⟨992728238397828576833773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5294550604788419076446789 992728238397828576833773)
                    ·
                      rfl

theorem cell23_5799994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 3, 4].length) (baseStart_5799994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5799994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5799994 prefixEnd_5799994 := by exact prefixLift 5799994
  have htrace : WordTrace (prefixWord ++ tailWord_5799994) baseStart_5799994 baseEnd_5799994 := by
    simpa [prefixWord, tailWord_5799994, baseEnd_5799994] using wordTrace_append hprefix tailTrace_5799994
  have hstable : (prefixWord ++ tailWord_5799994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5799994).length < 2 ^ (prefixWord ++ tailWord_5799994).sum := by decide
  have hdescent : baseEnd_5799994 < baseStart_5799994 := by decide
  rcases family_descends (prefixWord ++ tailWord_5799994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5800001 : List Nat := [1, 2, 5, 1, 2, 1, 1, 1, 1, 6, 2]
def baseStart_5800001 : Nat := 118140960795 + 5800001 * 2 ^ 59
def prefixEnd_5800001 : Nat := 4983230072969 + 3 ^ 40 * 5800001 * 2
def baseEnd_5800001 : Nat := 2978188309558067203113787

theorem tailTrace_5800001 : CollatzResearch.WordTrace tailWord_5800001 prefixEnd_5800001 2978188309558067203113787 := by
  unfold tailWord_5800001
  simp only [CollatzResearch.WordTrace]
  refine ⟨211543415460594413153295857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141028943640396275435530571 211543415460594413153295857)
  ·
    refine ⟨158657561595445809864971893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211543415460594413153295857 158657561595445809864971893)
    ·
      refine ⟨14874146399573044674841115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 158657561595445809864971893 14874146399573044674841115)
      ·
        refine ⟨22311219599359567012261673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14874146399573044674841115 22311219599359567012261673)
        ·
          refine ⟨16733414699519675259196255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22311219599359567012261673 16733414699519675259196255)
          ·
            refine ⟨25100122049279512888794383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16733414699519675259196255 25100122049279512888794383)
            ·
              refine ⟨37650183073919269333191575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25100122049279512888794383 37650183073919269333191575)
              ·
                refine ⟨56475274610878903999787363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37650183073919269333191575 56475274610878903999787363)
                ·
                  refine ⟨84712911916318355999681045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56475274610878903999787363 84712911916318355999681045)
                  ·
                    refine ⟨3970917746077422937485049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 84712911916318355999681045 3970917746077422937485049)
                    ·
                      refine ⟨2978188309558067203113787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3970917746077422937485049 2978188309558067203113787)
                      ·
                        rfl

theorem cell23_5800001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_5800001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5800001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5800001 prefixEnd_5800001 := by exact prefixLift 5800001
  have htrace : WordTrace (prefixWord ++ tailWord_5800001) baseStart_5800001 baseEnd_5800001 := by
    simpa [prefixWord, tailWord_5800001, baseEnd_5800001] using wordTrace_append hprefix tailTrace_5800001
  have hstable : (prefixWord ++ tailWord_5800001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5800001).length < 2 ^ (prefixWord ++ tailWord_5800001).sum := by decide
  have hdescent : baseEnd_5800001 < baseStart_5800001 := by decide
  rcases family_descends (prefixWord ++ tailWord_5800001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5800018 : List Nat := [3, 2, 2, 1, 4, 2, 1, 1, 2, 1, 4]
def baseStart_5800018 : Nat := 118140960795 + 5800018 * 2 ^ 59
def prefixEnd_5800018 : Nat := 4983230072969 + 3 ^ 40 * 5800018 * 2
def baseEnd_5800018 : Nat := 2978197038729193636601209

theorem tailTrace_5800018 : CollatzResearch.WordTrace tailWord_5800018 prefixEnd_5800018 2978197038729193636601209 := by
  unfold tailWord_5800018
  simp only [CollatzResearch.WordTrace]
  refine ⟨52886008875383206264166177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141029357001021883371109805 52886008875383206264166177)
  ·
    refine ⟨39664506656537404698124633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52886008875383206264166177 39664506656537404698124633)
    ·
      refine ⟨29748379992403053523593475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39664506656537404698124633 29748379992403053523593475)
      ·
        refine ⟨44622569988604580285390213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29748379992403053523593475 44622569988604580285390213)
        ·
          refine ⟨8366731872863358803510665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44622569988604580285390213 8366731872863358803510665)
          ·
            refine ⟨6275048904647519102632999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8366731872863358803510665 6275048904647519102632999)
            ·
              refine ⟨9412573356971278653949499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6275048904647519102632999 9412573356971278653949499)
              ·
                refine ⟨14118860035456917980924249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9412573356971278653949499 14118860035456917980924249)
                ·
                  refine ⟨10589145026592688485693187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14118860035456917980924249 10589145026592688485693187)
                  ·
                    refine ⟨15883717539889032728539781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10589145026592688485693187 15883717539889032728539781)
                    ·
                      refine ⟨2978197038729193636601209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15883717539889032728539781 2978197038729193636601209)
                      ·
                        rfl

theorem cell23_5800018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_5800018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5800018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5800018 prefixEnd_5800018 := by exact prefixLift 5800018
  have htrace : WordTrace (prefixWord ++ tailWord_5800018) baseStart_5800018 baseEnd_5800018 := by
    simpa [prefixWord, tailWord_5800018, baseEnd_5800018] using wordTrace_append hprefix tailTrace_5800018
  have hstable : (prefixWord ++ tailWord_5800018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5800018).length < 2 ^ (prefixWord ++ tailWord_5800018).sum := by decide
  have hdescent : baseEnd_5800018 < baseStart_5800018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5800018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5800021 : List Nat := [1, 3, 2, 2, 1, 3, 3, 1, 2, 2, 3]
def baseStart_5800021 : Nat := 118140960795 + 5800021 * 2 ^ 59
def prefixEnd_5800021 : Nat := 4983230072969 + 3 ^ 40 * 5800021 * 2
def baseEnd_5800021 : Nat := 2978198579171157124863695

theorem tailTrace_5800021 : CollatzResearch.WordTrace tailWord_5800021 prefixEnd_5800021 2978198579171157124863695 := by
  unfold tailWord_5800021
  simp only [CollatzResearch.WordTrace]
  refine ⟨211544144920521956569023917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141029429947014637712682611 211544144920521956569023917)
  ·
    refine ⟨79329054345195733713383969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211544144920521956569023917 79329054345195733713383969)
    ·
      refine ⟨59496790758896800285037977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79329054345195733713383969 59496790758896800285037977)
      ·
        refine ⟨44622593069172600213778483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59496790758896800285037977 44622593069172600213778483)
        ·
          refine ⟨66933889603758900320667725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44622593069172600213778483 66933889603758900320667725)
          ·
            refine ⟨25100208601409587620250397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66933889603758900320667725 25100208601409587620250397)
            ·
              refine ⟨9412578225528595357593899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25100208601409587620250397 9412578225528595357593899)
              ·
                refine ⟨14118867338292893036390849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9412578225528595357593899 14118867338292893036390849)
                ·
                  refine ⟨10589150503719669777293137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14118867338292893036390849 10589150503719669777293137)
                  ·
                    refine ⟨7941862877789752332969853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10589150503719669777293137 7941862877789752332969853)
                    ·
                      refine ⟨2978198579171157124863695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7941862877789752332969853 2978198579171157124863695)
                      ·
                        rfl

theorem cell23_5800021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_5800021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5800021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5800021 prefixEnd_5800021 := by exact prefixLift 5800021
  have htrace : WordTrace (prefixWord ++ tailWord_5800021) baseStart_5800021 baseEnd_5800021 := by
    simpa [prefixWord, tailWord_5800021, baseEnd_5800021] using wordTrace_append hprefix tailTrace_5800021
  have hstable : (prefixWord ++ tailWord_5800021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5800021).length < 2 ^ (prefixWord ++ tailWord_5800021).sum := by decide
  have hdescent : baseEnd_5800021 < baseStart_5800021 := by decide
  rcases family_descends (prefixWord ++ tailWord_5800021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5800028 : List Nat := [2, 2, 4, 1, 1, 2, 1, 5, 1, 4]
def baseStart_5800028 : Nat := 118140960795 + 5800028 * 2 ^ 59
def prefixEnd_5800028 : Nat := 4983230072969 + 3 ^ 40 * 5800028 * 2
def baseEnd_5800028 : Nat := 992734057845246199158721

theorem tailTrace_5800028 : CollatzResearch.WordTrace tailWord_5800028 prefixEnd_5800028 992734057845246199158721 := by
  unfold tailWord_5800028
  simp only [CollatzResearch.WordTrace]
  refine ⟨105772200115748298382264369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141029600154331064509685825 105772200115748298382264369)
  ·
    refine ⟨79329150086811223786698277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105772200115748298382264369 79329150086811223786698277)
    ·
      refine ⟨14874215641277104460005927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79329150086811223786698277 14874215641277104460005927)
      ·
        refine ⟨22311323461915656690008891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14874215641277104460005927 22311323461915656690008891)
        ·
          refine ⟨33466985192873485035013337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22311323461915656690008891 33466985192873485035013337)
          ·
            refine ⟨25100238894655113776260003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33466985192873485035013337 25100238894655113776260003)
            ·
              refine ⟨37650358341982670664390005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25100238894655113776260003 37650358341982670664390005)
              ·
                refine ⟨3529721094560875374786563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37650358341982670664390005 3529721094560875374786563)
                ·
                  refine ⟨5294581641841313062179845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3529721094560875374786563 5294581641841313062179845)
                  ·
                    refine ⟨992734057845246199158721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5294581641841313062179845 992734057845246199158721)
                    ·
                      rfl

theorem cell23_5800028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_5800028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5800028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5800028 prefixEnd_5800028 := by exact prefixLift 5800028
  have htrace : WordTrace (prefixWord ++ tailWord_5800028) baseStart_5800028 baseEnd_5800028 := by
    simpa [prefixWord, tailWord_5800028, baseEnd_5800028] using wordTrace_append hprefix tailTrace_5800028
  have hstable : (prefixWord ++ tailWord_5800028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5800028).length < 2 ^ (prefixWord ++ tailWord_5800028).sum := by decide
  have hdescent : baseEnd_5800028 < baseStart_5800028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5800028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5800061 : List Nat := [1, 4, 1, 1, 3, 2, 1, 2, 1, 5, 2]
def baseStart_5800061 : Nat := 118140960795 + 5800061 * 2 ^ 59
def prefixEnd_5800061 : Nat := 4983230072969 + 3 ^ 40 * 5800061 * 2
def baseEnd_5800061 : Nat := 2978219118397336968363511

theorem tailTrace_5800061 : CollatzResearch.WordTrace tailWord_5800061 prefixEnd_5800061 2978219118397336968363511 := by
  unfold tailWord_5800061
  simp only [CollatzResearch.WordTrace]
  refine ⟨211545603840377043400480037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141030402560251362266986691 211545603840377043400480037)
  ·
    refine ⟨39664800720070695637590007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 211545603840377043400480037 39664800720070695637590007)
    ·
      refine ⟨59497201080106043456385011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39664800720070695637590007 59497201080106043456385011)
      ·
        refine ⟨89245801620159065184577517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59497201080106043456385011 89245801620159065184577517)
        ·
          refine ⟨33467175607559649444216569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89245801620159065184577517 33467175607559649444216569)
          ·
            refine ⟨25100381705669737083162427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33467175607559649444216569 25100381705669737083162427)
            ·
              refine ⟨37650572558504605624743641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25100381705669737083162427 37650572558504605624743641)
              ·
                refine ⟨28237929418878454218557731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37650572558504605624743641 28237929418878454218557731)
                ·
                  refine ⟨42356894128317681327836597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28237929418878454218557731 42356894128317681327836597)
                  ·
                    refine ⟨3970958824529782624484681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42356894128317681327836597 3970958824529782624484681)
                    ·
                      refine ⟨2978219118397336968363511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3970958824529782624484681 2978219118397336968363511)
                      ·
                        rfl

theorem cell23_5800061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 5, 2].length) (baseStart_5800061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5800061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5800061 prefixEnd_5800061 := by exact prefixLift 5800061
  have htrace : WordTrace (prefixWord ++ tailWord_5800061) baseStart_5800061 baseEnd_5800061 := by
    simpa [prefixWord, tailWord_5800061, baseEnd_5800061] using wordTrace_append hprefix tailTrace_5800061
  have hstable : (prefixWord ++ tailWord_5800061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5800061).length < 2 ^ (prefixWord ++ tailWord_5800061).sum := by decide
  have hdescent : baseEnd_5800061 < baseStart_5800061 := by decide
  rcases family_descends (prefixWord ++ tailWord_5800061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5800101 : List Nat := [1, 3, 1, 2, 1, 3, 2, 4, 2, 4]
def baseStart_5800101 : Nat := 118140960795 + 5800101 * 2 ^ 59
def prefixEnd_5800101 : Nat := 4983230072969 + 3 ^ 40 * 5800101 * 2
def baseEnd_5800101 : Nat := 992746552541172270621109

theorem tailTrace_5800101 : CollatzResearch.WordTrace tailWord_5800101 prefixEnd_5800101 992746552541172270621109 := by
  unfold tailWord_5800101
  simp only [CollatzResearch.WordTrace]
  refine ⟨211547062760232130231936157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141031375173488086821290771 211547062760232130231936157)
  ·
    refine ⟨79330148535087048836976059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211547062760232130231936157 79330148535087048836976059)
    ·
      refine ⟨118995222802630573255464089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79330148535087048836976059 118995222802630573255464089)
      ·
        refine ⟨89246417101972929941598067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118995222802630573255464089 89246417101972929941598067)
        ·
          refine ⟨133869625652959394912397101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89246417101972929941598067 133869625652959394912397101)
          ·
            refine ⟨50201109619859773092148913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133869625652959394912397101 50201109619859773092148913)
            ·
              refine ⟨37650832214894829819111685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50201109619859773092148913 37650832214894829819111685)
              ·
                refine ⟨7059531040292780591083441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37650832214894829819111685 7059531040292780591083441)
                ·
                  refine ⟨5294648280219585443312581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7059531040292780591083441 5294648280219585443312581)
                  ·
                    refine ⟨992746552541172270621109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5294648280219585443312581 992746552541172270621109)
                    ·
                      rfl

theorem cell23_5800101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 4, 2, 4].length) (baseStart_5800101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5800101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5800101 prefixEnd_5800101 := by exact prefixLift 5800101
  have htrace : WordTrace (prefixWord ++ tailWord_5800101) baseStart_5800101 baseEnd_5800101 := by
    simpa [prefixWord, tailWord_5800101, baseEnd_5800101] using wordTrace_append hprefix tailTrace_5800101
  have hstable : (prefixWord ++ tailWord_5800101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5800101).length < 2 ^ (prefixWord ++ tailWord_5800101).sum := by decide
  have hdescent : baseEnd_5800101 < baseStart_5800101 := by decide
  rcases family_descends (prefixWord ++ tailWord_5800101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5800114 : List Nat := [3, 2, 1, 1, 1, 3, 4, 8]
def baseStart_5800114 : Nat := 118140960795 + 5800114 * 2 ^ 59
def prefixEnd_5800114 : Nat := 4983230072969 + 3 ^ 40 * 5800114 * 2
def baseEnd_5800114 : Nat := 110305419736000935592621

theorem tailTrace_5800114 : CollatzResearch.WordTrace tailWord_5800114 prefixEnd_5800114 110305419736000935592621 := by
  unfold tailWord_5800114
  simp only [CollatzResearch.WordTrace]
  refine ⟨52886884227296258363039849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141031691272790022301439597 52886884227296258363039849)
  ·
    refine ⟨39665163170472193772279887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52886884227296258363039849 39665163170472193772279887)
    ·
      refine ⟨59497744755708290658419831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39665163170472193772279887 59497744755708290658419831)
      ·
        refine ⟨89246617133562435987629747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59497744755708290658419831 89246617133562435987629747)
        ·
          refine ⟨133869925700343653981444621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89246617133562435987629747 133869925700343653981444621)
          ·
            refine ⟨50201222137628870243041733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133869925700343653981444621 50201222137628870243041733)
            ·
              refine ⟨9412729150805413170570325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50201222137628870243041733 9412729150805413170570325)
              ·
                refine ⟨110305419736000935592621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9412729150805413170570325 110305419736000935592621)
                ·
                  rfl

theorem cell23_5800114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 8].length) (baseStart_5800114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5800114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5800114 prefixEnd_5800114 := by exact prefixLift 5800114
  have htrace : WordTrace (prefixWord ++ tailWord_5800114) baseStart_5800114 baseEnd_5800114 := by
    simpa [prefixWord, tailWord_5800114, baseEnd_5800114] using wordTrace_append hprefix tailTrace_5800114
  have hstable : (prefixWord ++ tailWord_5800114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5800114).length < 2 ^ (prefixWord ++ tailWord_5800114).sum := by decide
  have hdescent : baseEnd_5800114 < baseStart_5800114 := by decide
  rcases family_descends (prefixWord ++ tailWord_5800114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5800128 : List Nat := [2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 3]
def baseStart_5800128 : Nat := 118140960795 + 5800128 * 2 ^ 59
def prefixEnd_5800128 : Nat := 4983230072969 + 3 ^ 40 * 5800128 * 2
def baseEnd_5800128 : Nat := 2978253521601188206225703

theorem tailTrace_5800128 : CollatzResearch.WordTrace tailWord_5800128 prefixEnd_5800128 2978253521601188206225703 := by
  unfold tailWord_5800128
  simp only [CollatzResearch.WordTrace]
  refine ⟨105774023765567156921584519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141032031687422875895446025 105774023765567156921584519)
  ·
    refine ⟨158661035648350735382376779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105774023765567156921584519 158661035648350735382376779)
    ·
      refine ⟨237991553472526103073565169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158661035648350735382376779 237991553472526103073565169)
      ·
        refine ⟨178493665104394577305173877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237991553472526103073565169 178493665104394577305173877)
        ·
          refine ⟨16733781103536991622360051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 178493665104394577305173877 16733781103536991622360051)
          ·
            refine ⟨25100671655305487433540077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16733781103536991622360051 25100671655305487433540077)
            ·
              refine ⟨9412751870739557787577529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25100671655305487433540077 9412751870739557787577529)
              ·
                refine ⟨7059563903054668340683147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9412751870739557787577529 7059563903054668340683147)
                ·
                  refine ⟨10589345854582002511024721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7059563903054668340683147 10589345854582002511024721)
                  ·
                    refine ⟨7942009390936501883268541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10589345854582002511024721 7942009390936501883268541)
                    ·
                      refine ⟨2978253521601188206225703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7942009390936501883268541 2978253521601188206225703)
                      ·
                        rfl

theorem cell23_5800128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 3].length) (baseStart_5800128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5800128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5800128 prefixEnd_5800128 := by exact prefixLift 5800128
  have htrace : WordTrace (prefixWord ++ tailWord_5800128) baseStart_5800128 baseEnd_5800128 := by
    simpa [prefixWord, tailWord_5800128, baseEnd_5800128] using wordTrace_append hprefix tailTrace_5800128
  have hstable : (prefixWord ++ tailWord_5800128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5800128).length < 2 ^ (prefixWord ++ tailWord_5800128).sum := by decide
  have hdescent : baseEnd_5800128 < baseStart_5800128 := by decide
  rcases family_descends (prefixWord ++ tailWord_5800128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5800154 : List Nat := [3, 1, 1, 2, 2, 1, 2, 2, 2, 2, 5]
def baseStart_5800154 : Nat := 118140960795 + 5800154 * 2 ^ 59
def prefixEnd_5800154 : Nat := 4983230072969 + 3 ^ 40 * 5800154 * 2
def baseEnd_5800154 : Nat := 2978266872098205104500583

theorem tailTrace_5800154 : CollatzResearch.WordTrace tailWord_5800154 prefixEnd_5800154 2978266872098205104500583 := by
  unfold tailWord_5800154
  simp only [CollatzResearch.WordTrace]
  refine ⟨52887248957260030070903879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141032663886026746855743677 52887248957260030070903879)
  ·
    refine ⟨79330873435890045106355819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52887248957260030070903879 79330873435890045106355819)
    ·
      refine ⟨118996310153835067659533729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79330873435890045106355819 118996310153835067659533729)
      ·
        refine ⟨89247232615376300744650297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118996310153835067659533729 89247232615376300744650297)
        ·
          refine ⟨66935424461532225558487723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89247232615376300744650297 66935424461532225558487723)
          ·
            refine ⟨100403136692298338337731585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66935424461532225558487723 100403136692298338337731585)
            ·
              refine ⟨75302352519223753753298689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100403136692298338337731585 75302352519223753753298689)
              ·
                refine ⟨56476764389417815314974017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75302352519223753753298689 56476764389417815314974017)
                ·
                  refine ⟨42357573292063361486230513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56476764389417815314974017 42357573292063361486230513)
                  ·
                    refine ⟨31768179969047521114672885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42357573292063361486230513 31768179969047521114672885)
                    ·
                      refine ⟨2978266872098205104500583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31768179969047521114672885 2978266872098205104500583)
                      ·
                        rfl

theorem cell23_5800154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_5800154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5800154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5800154 prefixEnd_5800154 := by exact prefixLift 5800154
  have htrace : WordTrace (prefixWord ++ tailWord_5800154) baseStart_5800154 baseEnd_5800154 := by
    simpa [prefixWord, tailWord_5800154, baseEnd_5800154] using wordTrace_append hprefix tailTrace_5800154
  have hstable : (prefixWord ++ tailWord_5800154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5800154).length < 2 ^ (prefixWord ++ tailWord_5800154).sum := by decide
  have hdescent : baseEnd_5800154 < baseStart_5800154 := by decide
  rcases family_descends (prefixWord ++ tailWord_5800154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5800168 : List Nat := [2, 1, 4, 1, 2, 2, 1, 2, 3, 3, 2]
def baseStart_5800168 : Nat := 118140960795 + 5800168 * 2 ^ 59
def prefixEnd_5800168 : Nat := 4983230072969 + 3 ^ 40 * 5800168 * 2
def baseEnd_5800168 : Nat := 2978274060827368049725519

theorem tailTrace_5800168 : CollatzResearch.WordTrace tailWord_5800168 prefixEnd_5800168 2978274060827368049725519 := by
  unfold tailWord_5800168
  simp only [CollatzResearch.WordTrace]
  refine ⟨105774753225494700337312579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141033004300659600449750105 105774753225494700337312579)
  ·
    refine ⟨158662129838242050505968869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105774753225494700337312579 158662129838242050505968869)
    ·
      refine ⟨29749149344670384469869163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158662129838242050505968869 29749149344670384469869163)
      ·
        refine ⟨44623724017005576704803745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29749149344670384469869163 44623724017005576704803745)
        ·
          refine ⟨33467793012754182528602809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44623724017005576704803745 33467793012754182528602809)
          ·
            refine ⟨25100844759565636896452107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33467793012754182528602809 25100844759565636896452107)
            ·
              refine ⟨37651267139348455344678161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25100844759565636896452107 37651267139348455344678161)
              ·
                refine ⟨28238450354511341508508621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37651267139348455344678161 28238450354511341508508621)
                ·
                  refine ⟨10589418882941753065690733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28238450354511341508508621 10589418882941753065690733)
                  ·
                    refine ⟨3971032081103157399634025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10589418882941753065690733 3971032081103157399634025)
                    ·
                      refine ⟨2978274060827368049725519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3971032081103157399634025 2978274060827368049725519)
                      ·
                        rfl

theorem cell23_5800168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 3, 3, 2].length) (baseStart_5800168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5800168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5800168 prefixEnd_5800168 := by exact prefixLift 5800168
  have htrace : WordTrace (prefixWord ++ tailWord_5800168) baseStart_5800168 baseEnd_5800168 := by
    simpa [prefixWord, tailWord_5800168, baseEnd_5800168] using wordTrace_append hprefix tailTrace_5800168
  have hstable : (prefixWord ++ tailWord_5800168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5800168).length < 2 ^ (prefixWord ++ tailWord_5800168).sum := by decide
  have hdescent : baseEnd_5800168 < baseStart_5800168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5800168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5800184 : List Nat := [2, 1, 2, 1, 1, 2, 1, 3, 4, 1, 5]
def baseStart_5800184 : Nat := 118140960795 + 5800184 * 2 ^ 59
def prefixEnd_5800184 : Nat := 4983230072969 + 3 ^ 40 * 5800184 * 2
def baseEnd_5800184 : Nat := 2978282276517839987125445

theorem tailTrace_5800184 : CollatzResearch.WordTrace tailWord_5800184 prefixEnd_5800184 2978282276517839987125445 := by
  unfold tailWord_5800184
  simp only [CollatzResearch.WordTrace]
  refine ⟨105775045009465717703603803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141033393345954290271471737 105775045009465717703603803)
  ·
    refine ⟨158662567514198576555405705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105775045009465717703603803 158662567514198576555405705)
    ·
      refine ⟨118996925635648932416554279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158662567514198576555405705 118996925635648932416554279)
      ·
        refine ⟨178495388453473398624831419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118996925635648932416554279 178495388453473398624831419)
        ·
          refine ⟨267743082680210097937247129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178495388453473398624831419 267743082680210097937247129)
          ·
            refine ⟨200807312010157573452935347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267743082680210097937247129 200807312010157573452935347)
            ·
              refine ⟨301210968015236360179403021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200807312010157573452935347 301210968015236360179403021)
              ·
                refine ⟨112954113005713635067276133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 301210968015236360179403021 112954113005713635067276133)
                ·
                  refine ⟨21178896188571306575114275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 112954113005713635067276133 21178896188571306575114275)
                  ·
                    refine ⟨31768344282856959862671413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21178896188571306575114275 31768344282856959862671413)
                    ·
                      refine ⟨2978282276517839987125445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31768344282856959862671413 2978282276517839987125445)
                      ·
                        rfl

theorem cell23_5800184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 4, 1, 5].length) (baseStart_5800184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5800184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5800184 prefixEnd_5800184 := by exact prefixLift 5800184
  have htrace : WordTrace (prefixWord ++ tailWord_5800184) baseStart_5800184 baseEnd_5800184 := by
    simpa [prefixWord, tailWord_5800184, baseEnd_5800184] using wordTrace_append hprefix tailTrace_5800184
  have hstable : (prefixWord ++ tailWord_5800184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5800184).length < 2 ^ (prefixWord ++ tailWord_5800184).sum := by decide
  have hdescent : baseEnd_5800184 < baseStart_5800184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5800184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5800204 : List Nat := [2, 2, 1, 2, 2, 2, 1, 2, 9]
def baseStart_5800204 : Nat := 118140960795 + 5800204 * 2 ^ 59
def prefixEnd_5800204 : Nat := 4983230072969 + 3 ^ 40 * 5800204 * 2
def baseEnd_5800204 : Nat := 330921394014547767652817

theorem tailTrace_5800204 : CollatzResearch.WordTrace tailWord_5800204 prefixEnd_5800204 330921394014547767652817 := by
  unfold tailWord_5800204
  simp only [CollatzResearch.WordTrace]
  refine ⟨105775409739429489411467833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141033879652572652548623777 105775409739429489411467833)
  ·
    refine ⟨79331557304572117058600875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105775409739429489411467833 79331557304572117058600875)
    ·
      refine ⟨118997335956858175587901313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79331557304572117058600875 118997335956858175587901313)
      ·
        refine ⟨89248001967643631690925985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118997335956858175587901313 89248001967643631690925985)
        ·
          refine ⟨66936001475732723768194489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89248001967643631690925985 66936001475732723768194489)
          ·
            refine ⟨50202001106799542826145867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66936001475732723768194489 50202001106799542826145867)
            ·
              refine ⟨75303001660199314239218801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50202001106799542826145867 75303001660199314239218801)
              ·
                refine ⟨56477251245149485679414101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75303001660199314239218801 56477251245149485679414101)
                ·
                  refine ⟨330921394014547767652817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 56477251245149485679414101 330921394014547767652817)
                  ·
                    rfl

theorem cell23_5800204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 9].length) (baseStart_5800204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5800204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5800204 prefixEnd_5800204 := by exact prefixLift 5800204
  have htrace : WordTrace (prefixWord ++ tailWord_5800204) baseStart_5800204 baseEnd_5800204 := by
    simpa [prefixWord, tailWord_5800204, baseEnd_5800204] using wordTrace_append hprefix tailTrace_5800204
  have hstable : (prefixWord ++ tailWord_5800204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5800204).length < 2 ^ (prefixWord ++ tailWord_5800204).sum := by decide
  have hdescent : baseEnd_5800204 < baseStart_5800204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5800204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5800215 : List Nat := [1, 1, 3, 4, 1, 3, 1, 1, 4, 2, 2]
def baseStart_5800215 : Nat := 118140960795 + 5800215 * 2 ^ 59
def prefixEnd_5800215 : Nat := 4983230072969 + 3 ^ 40 * 5800215 * 2
def baseEnd_5800215 : Nat := 2978298194418129365837803

theorem tailTrace_5800215 : CollatzResearch.WordTrace tailWord_5800215 prefixEnd_5800215 2978298194418129365837803 := by
  unfold tailWord_5800215
  simp only [CollatzResearch.WordTrace]
  refine ⟨211551220681819127701586099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141034147121212751801057399 211551220681819127701586099)
  ·
    refine ⟨317326831022728691552379149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211551220681819127701586099 317326831022728691552379149)
    ·
      refine ⟨118997561633523259332142181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 317326831022728691552379149 118997561633523259332142181)
      ·
        refine ⟨22312042806285611124776659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118997561633523259332142181 22312042806285611124776659)
        ·
          refine ⟨33468064209428416687164989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22312042806285611124776659 33468064209428416687164989)
          ·
            refine ⟨12550524078535656257686871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33468064209428416687164989 12550524078535656257686871)
            ·
              refine ⟨18825786117803484386530307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12550524078535656257686871 18825786117803484386530307)
              ·
                refine ⟨28238679176705226579795461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18825786117803484386530307 28238679176705226579795461)
                ·
                  refine ⟨5294752345632229983711649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28238679176705226579795461 5294752345632229983711649)
                  ·
                    refine ⟨3971064259224172487783737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5294752345632229983711649 3971064259224172487783737)
                    ·
                      refine ⟨2978298194418129365837803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3971064259224172487783737 2978298194418129365837803)
                      ·
                        rfl

theorem cell23_5800215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_5800215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5800215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5800215 prefixEnd_5800215 := by exact prefixLift 5800215
  have htrace : WordTrace (prefixWord ++ tailWord_5800215) baseStart_5800215 baseEnd_5800215 := by
    simpa [prefixWord, tailWord_5800215, baseEnd_5800215] using wordTrace_append hprefix tailTrace_5800215
  have hstable : (prefixWord ++ tailWord_5800215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5800215).length < 2 ^ (prefixWord ++ tailWord_5800215).sum := by decide
  have hdescent : baseEnd_5800215 < baseStart_5800215 := by decide
  rcases family_descends (prefixWord ++ tailWord_5800215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5800232 : List Nat := [2, 1, 5, 1, 3, 2, 1, 1, 1, 4, 2]
def baseStart_5800232 : Nat := 118140960795 + 5800232 * 2 ^ 59
def prefixEnd_5800232 : Nat := 4983230072969 + 3 ^ 40 * 5800232 * 2
def baseEnd_5800232 : Nat := 2978306923589255799325225

theorem tailTrace_5800232 : CollatzResearch.WordTrace tailWord_5800232 prefixEnd_5800232 2978306923589255799325225 := by
  unfold tailWord_5800232
  simp only [CollatzResearch.WordTrace]
  refine ⟨105775920361378769802477475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141034560481838359736636633 105775920361378769802477475)
  ·
    refine ⟨158663880542068154703716213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105775920361378769802477475 158663880542068154703716213)
    ·
      refine ⟨14874738800818889503473395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 158663880542068154703716213 14874738800818889503473395)
      ·
        refine ⟨22312108201228334255210093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14874738800818889503473395 22312108201228334255210093)
        ·
          refine ⟨8367040575460625345703785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22312108201228334255210093 8367040575460625345703785)
          ·
            refine ⟨6275280431595469009277839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8367040575460625345703785 6275280431595469009277839)
            ·
              refine ⟨9412920647393203513916759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6275280431595469009277839 9412920647393203513916759)
              ·
                refine ⟨14119380971089805270875139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9412920647393203513916759 14119380971089805270875139)
                ·
                  refine ⟨21179071456634707906312709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14119380971089805270875139 21179071456634707906312709)
                  ·
                    refine ⟨3971075898119007732433633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21179071456634707906312709 3971075898119007732433633)
                    ·
                      refine ⟨2978306923589255799325225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3971075898119007732433633 2978306923589255799325225)
                      ·
                        rfl

theorem cell23_5800232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_5800232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5800232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5800232 prefixEnd_5800232 := by exact prefixLift 5800232
  have htrace : WordTrace (prefixWord ++ tailWord_5800232) baseStart_5800232 baseEnd_5800232 := by
    simpa [prefixWord, tailWord_5800232, baseEnd_5800232] using wordTrace_append hprefix tailTrace_5800232
  have hstable : (prefixWord ++ tailWord_5800232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5800232).length < 2 ^ (prefixWord ++ tailWord_5800232).sum := by decide
  have hdescent : baseEnd_5800232 < baseStart_5800232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5800232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5800328 : List Nat := [2, 1, 3, 3, 1, 1, 4, 2, 6]
def baseStart_5800328 : Nat := 118140960795 + 5800328 * 2 ^ 59
def prefixEnd_5800328 : Nat := 4983230072969 + 3 ^ 40 * 5800328 * 2
def baseEnd_5800328 : Nat := 330928468636898602636087

theorem tailTrace_5800328 : CollatzResearch.WordTrace tailWord_5800328 prefixEnd_5800328 330928468636898602636087 := by
  unfold tailWord_5800328
  simp only [CollatzResearch.WordTrace]
  refine ⟨105777671065204874000224819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141036894753606498666966425 105777671065204874000224819)
  ·
    refine ⟨158666506597807311000337229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105777671065204874000224819 158666506597807311000337229)
    ·
      refine ⟨59499939974177741625126461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158666506597807311000337229 59499939974177741625126461)
      ·
        refine ⟨22312477490316653109422423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59499939974177741625126461 22312477490316653109422423)
        ·
          refine ⟨33468716235474979664133635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22312477490316653109422423 33468716235474979664133635)
          ·
            refine ⟨50203074353212469496200453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33468716235474979664133635 50203074353212469496200453)
            ·
              refine ⟨9413076441227338030537585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50203074353212469496200453 9413076441227338030537585)
              ·
                refine ⟨7059807330920503522903189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9413076441227338030537585 7059807330920503522903189)
                ·
                  refine ⟨330928468636898602636087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7059807330920503522903189 330928468636898602636087)
                  ·
                    rfl

theorem cell23_5800328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 2, 6].length) (baseStart_5800328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5800328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5800328 prefixEnd_5800328 := by exact prefixLift 5800328
  have htrace : WordTrace (prefixWord ++ tailWord_5800328) baseStart_5800328 baseEnd_5800328 := by
    simpa [prefixWord, tailWord_5800328, baseEnd_5800328] using wordTrace_append hprefix tailTrace_5800328
  have hstable : (prefixWord ++ tailWord_5800328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5800328).length < 2 ^ (prefixWord ++ tailWord_5800328).sum := by decide
  have hdescent : baseEnd_5800328 < baseStart_5800328 := by decide
  rcases family_descends (prefixWord ++ tailWord_5800328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5800332 : List Nat := [2, 2, 1, 2, 1, 4, 4, 2, 1, 4]
def baseStart_5800332 : Nat := 118140960795 + 5800332 * 2 ^ 59
def prefixEnd_5800332 : Nat := 4983230072969 + 3 ^ 40 * 5800332 * 2
def baseEnd_5800332 : Nat := 992786090551568469358255

theorem tailTrace_5800332 : CollatzResearch.WordTrace tailWord_5800332 prefixEnd_5800332 992786090551568469358255 := by
  unfold tailWord_5800332
  simp only [CollatzResearch.WordTrace]
  refine ⟨105777744011197628341797625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141036992014930171122396833 105777744011197628341797625)
  ·
    refine ⟨79333308008398221256348219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105777744011197628341797625 79333308008398221256348219)
    ·
      refine ⟨118999962012597331884522329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79333308008398221256348219 118999962012597331884522329)
      ·
        refine ⟨89249971509447998913391747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118999962012597331884522329 89249971509447998913391747)
        ·
          refine ⟨133874957264171998370087621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89249971509447998913391747 133874957264171998370087621)
          ·
            refine ⟨25101554487032249694391429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 133874957264171998370087621 25101554487032249694391429)
            ·
              refine ⟨4706541466318546817698393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25101554487032249694391429 4706541466318546817698393)
              ·
                refine ⟨3529906099738910113273795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4706541466318546817698393 3529906099738910113273795)
                ·
                  refine ⟨5294859149608365169910693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3529906099738910113273795 5294859149608365169910693)
                  ·
                    refine ⟨992786090551568469358255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5294859149608365169910693 992786090551568469358255)
                    ·
                      rfl

theorem cell23_5800332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 2, 1, 4].length) (baseStart_5800332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5800332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5800332 prefixEnd_5800332 := by exact prefixLift 5800332
  have htrace : WordTrace (prefixWord ++ tailWord_5800332) baseStart_5800332 baseEnd_5800332 := by
    simpa [prefixWord, tailWord_5800332, baseEnd_5800332] using wordTrace_append hprefix tailTrace_5800332
  have hstable : (prefixWord ++ tailWord_5800332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5800332).length < 2 ^ (prefixWord ++ tailWord_5800332).sum := by decide
  have hdescent : baseEnd_5800332 < baseStart_5800332 := by decide
  rcases family_descends (prefixWord ++ tailWord_5800332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5800351 : List Nat := [1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 7]
def baseStart_5800351 : Nat := 118140960795 + 5800351 * 2 ^ 59
def prefixEnd_5800351 : Nat := 4983230072969 + 3 ^ 40 * 5800351 * 2
def baseEnd_5800351 : Nat := 2978368027787140833737177

theorem tailTrace_5800351 : CollatzResearch.WordTrace tailWord_5800351 prefixEnd_5800351 2978368027787140833737177 := by
  unfold tailWord_5800351
  simp only [CollatzResearch.WordTrace]
  refine ⟨211556181009326422928536907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141037454006217615285691271 211556181009326422928536907)
  ·
    refine ⟨317334271513989634392805361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211556181009326422928536907 317334271513989634392805361)
    ·
      refine ⟨238000703635492225794604021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317334271513989634392805361 238000703635492225794604021)
      ·
        refine ⟨22312565965827396168244127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 238000703635492225794604021 22312565965827396168244127)
        ·
          refine ⟨33468848948741094252366191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22312565965827396168244127 33468848948741094252366191)
          ·
            refine ⟨50203273423111641378549287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33468848948741094252366191 50203273423111641378549287)
            ·
              refine ⟨75304910134667462067823931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50203273423111641378549287 75304910134667462067823931)
              ·
                refine ⟨112957365202001193101735897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75304910134667462067823931 112957365202001193101735897)
                ·
                  refine ⟨84718023901500894826301923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112957365202001193101735897 84718023901500894826301923)
                  ·
                    refine ⟨127077035852251342239452885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 84718023901500894826301923 127077035852251342239452885)
                    ·
                      refine ⟨2978368027787140833737177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 127077035852251342239452885 2978368027787140833737177)
                      ·
                        rfl

theorem cell23_5800351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_5800351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5800351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5800351 prefixEnd_5800351 := by exact prefixLift 5800351
  have htrace : WordTrace (prefixWord ++ tailWord_5800351) baseStart_5800351 baseEnd_5800351 := by
    simpa [prefixWord, tailWord_5800351, baseEnd_5800351] using wordTrace_append hprefix tailTrace_5800351
  have hstable : (prefixWord ++ tailWord_5800351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5800351).length < 2 ^ (prefixWord ++ tailWord_5800351).sum := by decide
  have hdescent : baseEnd_5800351 < baseStart_5800351 := by decide
  rcases family_descends (prefixWord ++ tailWord_5800351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5800355 : List Nat := [1, 1, 1, 4, 1, 5, 1, 2, 3, 1, 3]
def baseStart_5800355 : Nat := 118140960795 + 5800355 * 2 ^ 59
def prefixEnd_5800355 : Nat := 4983230072969 + 3 ^ 40 * 5800355 * 2
def baseEnd_5800355 : Nat := 2978370081709758818087159

theorem tailTrace_5800355 : CollatzResearch.WordTrace tailWord_5800355 prefixEnd_5800355 2978370081709758818087159 := by
  unfold tailWord_5800355
  simp only [CollatzResearch.WordTrace]
  refine ⟨211556326901311931611682519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141037551267541287741121679 211556326901311931611682519)
  ·
    refine ⟨317334490351967897417523779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211556326901311931611682519 317334490351967897417523779)
    ·
      refine ⟨476001735527951846126285669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317334490351967897417523779 476001735527951846126285669)
      ·
        refine ⟨89250325411490971148678563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 476001735527951846126285669 89250325411490971148678563)
        ·
          refine ⟨133875488117236456723017845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89250325411490971148678563 133875488117236456723017845)
          ·
            refine ⟨12550827010990917817782923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 133875488117236456723017845 12550827010990917817782923)
            ·
              refine ⟨18826240516486376726674385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12550827010990917817782923 18826240516486376726674385)
              ·
                refine ⟨14119680387364782545005789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18826240516486376726674385 14119680387364782545005789)
                ·
                  refine ⟨5294880145261793454377171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14119680387364782545005789 5294880145261793454377171)
                  ·
                    refine ⟨7942320217892690181565757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5294880145261793454377171 7942320217892690181565757)
                    ·
                      refine ⟨2978370081709758818087159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7942320217892690181565757 2978370081709758818087159)
                      ·
                        rfl

theorem cell23_5800355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 3, 1, 3].length) (baseStart_5800355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5800355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5800355 prefixEnd_5800355 := by exact prefixLift 5800355
  have htrace : WordTrace (prefixWord ++ tailWord_5800355) baseStart_5800355 baseEnd_5800355 := by
    simpa [prefixWord, tailWord_5800355, baseEnd_5800355] using wordTrace_append hprefix tailTrace_5800355
  have hstable : (prefixWord ++ tailWord_5800355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5800355).length < 2 ^ (prefixWord ++ tailWord_5800355).sum := by decide
  have hdescent : baseEnd_5800355 < baseStart_5800355 := by decide
  rcases family_descends (prefixWord ++ tailWord_5800355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5800375 : List Nat := [1, 1, 3, 1, 3, 3, 4, 1, 1, 5]
def baseStart_5800375 : Nat := 118140960795 + 5800375 * 2 ^ 59
def prefixEnd_5800375 : Nat := 4983230072969 + 3 ^ 40 * 5800375 * 2
def baseEnd_5800375 : Nat := 992793450440949579945689

theorem tailTrace_5800375 : CollatzResearch.WordTrace tailWord_5800375 prefixEnd_5800375 992793450440949579945689 := by
  unfold tailWord_5800375
  simp only [CollatzResearch.WordTrace]
  refine ⟨211557056361239475027410579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141038037574159650018273719 211557056361239475027410579)
  ·
    refine ⟨317335584541859212541115869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211557056361239475027410579 317335584541859212541115869)
    ·
      refine ⟨119000844203197204702918451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 317335584541859212541115869 119000844203197204702918451)
      ·
        refine ⟨178501266304795807054377677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119000844203197204702918451 178501266304795807054377677)
        ·
          refine ⟨66937974864298427645391629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178501266304795807054377677 66937974864298427645391629)
          ·
            refine ⟨25101740574111910367021861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66937974864298427645391629 25101740574111910367021861)
            ·
              refine ⟨4706576357645983193816599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25101740574111910367021861 4706576357645983193816599)
              ·
                refine ⟨7059864536468974790724899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4706576357645983193816599 7059864536468974790724899)
                ·
                  refine ⟨10589796804703462186087349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7059864536468974790724899 10589796804703462186087349)
                  ·
                    refine ⟨992793450440949579945689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10589796804703462186087349 992793450440949579945689)
                    ·
                      rfl

theorem cell23_5800375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 1, 1, 5].length) (baseStart_5800375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5800375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5800375 prefixEnd_5800375 := by exact prefixLift 5800375
  have htrace : WordTrace (prefixWord ++ tailWord_5800375) baseStart_5800375 baseEnd_5800375 := by
    simpa [prefixWord, tailWord_5800375, baseEnd_5800375] using wordTrace_append hprefix tailTrace_5800375
  have hstable : (prefixWord ++ tailWord_5800375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5800375).length < 2 ^ (prefixWord ++ tailWord_5800375).sum := by decide
  have hdescent : baseEnd_5800375 < baseStart_5800375 := by decide
  rcases family_descends (prefixWord ++ tailWord_5800375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5800378 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 1, 8, 2]
def baseStart_5800378 : Nat := 118140960795 + 5800378 * 2 ^ 59
def prefixEnd_5800378 : Nat := 4983230072969 + 3 ^ 40 * 5800378 * 2
def baseEnd_5800378 : Nat := 2978381891764812228099553

theorem tailTrace_5800378 : CollatzResearch.WordTrace tailWord_5800378 prefixEnd_5800378 2978381891764812228099553 := by
  unfold tailWord_5800378
  simp only [CollatzResearch.WordTrace]
  refine ⟨52889291445057151634942447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141038110520152404359846525 52889291445057151634942447)
  ·
    refine ⟨79333937167585727452413671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52889291445057151634942447 79333937167585727452413671)
    ·
      refine ⟨119000905751378591178620507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79333937167585727452413671 119000905751378591178620507)
      ·
        refine ⟨178501358627067886767930761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119000905751378591178620507 178501358627067886767930761)
        ·
          refine ⟨133876018970300915075948071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178501358627067886767930761 133876018970300915075948071)
          ·
            refine ⟨200814028455451372613922107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133876018970300915075948071 200814028455451372613922107)
            ·
              refine ⟨301221042683177058920883161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200814028455451372613922107 301221042683177058920883161)
              ·
                refine ⟨225915782012382794190662371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 301221042683177058920883161 225915782012382794190662371)
                ·
                  refine ⟨338873673018574191285993557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 225915782012382794190662371 338873673018574191285993557)
                  ·
                    refine ⟨3971175855686416304132737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 338873673018574191285993557 3971175855686416304132737)
                    ·
                      refine ⟨2978381891764812228099553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3971175855686416304132737 2978381891764812228099553)
                      ·
                        rfl

theorem cell23_5800378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 1, 8, 2].length) (baseStart_5800378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5800378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5800378 prefixEnd_5800378 := by exact prefixLift 5800378
  have htrace : WordTrace (prefixWord ++ tailWord_5800378) baseStart_5800378 baseEnd_5800378 := by
    simpa [prefixWord, tailWord_5800378, baseEnd_5800378] using wordTrace_append hprefix tailTrace_5800378
  have hstable : (prefixWord ++ tailWord_5800378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5800378).length < 2 ^ (prefixWord ++ tailWord_5800378).sum := by decide
  have hdescent : baseEnd_5800378 < baseStart_5800378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5800378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5800405 : List Nat := [1, 3, 2, 3, 1, 4, 1, 1, 1, 6]
def baseStart_5800405 : Nat := 118140960795 + 5800405 * 2 ^ 59
def prefixEnd_5800405 : Nat := 4983230072969 + 3 ^ 40 * 5800405 * 2
def baseEnd_5800405 : Nat := 992798585247494540820643

theorem tailTrace_5800405 : CollatzResearch.WordTrace tailWord_5800405 prefixEnd_5800405 992798585247494540820643 := by
  unfold tailWord_5800405
  simp only [CollatzResearch.WordTrace]
  refine ⟨211558150551130790151002669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141038767034087193434001779 211558150551130790151002669)
  ·
    refine ⟨79334306456674046306626001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211558150551130790151002669 79334306456674046306626001)
    ·
      refine ⟨59500729842505534729969501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79334306456674046306626001 59500729842505534729969501)
      ·
        refine ⟨22312773690939575523738563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59500729842505534729969501 22312773690939575523738563)
        ·
          refine ⟨33469160536409363285607845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22312773690939575523738563 33469160536409363285607845)
          ·
            refine ⟨6275467600576755616051471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33469160536409363285607845 6275467600576755616051471)
            ·
              refine ⟨9413201400865133424077207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6275467600576755616051471 9413201400865133424077207)
              ·
                refine ⟨14119802101297700136115811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9413201400865133424077207 14119802101297700136115811)
                ·
                  refine ⟨21179703151946550204173717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14119802101297700136115811 21179703151946550204173717)
                  ·
                    refine ⟨992798585247494540820643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21179703151946550204173717 992798585247494540820643)
                    ·
                      rfl

theorem cell23_5800405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 6].length) (baseStart_5800405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5800405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5800405 prefixEnd_5800405 := by exact prefixLift 5800405
  have htrace : WordTrace (prefixWord ++ tailWord_5800405) baseStart_5800405 baseEnd_5800405 := by
    simpa [prefixWord, tailWord_5800405, baseEnd_5800405] using wordTrace_append hprefix tailTrace_5800405
  have hstable : (prefixWord ++ tailWord_5800405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5800405).length < 2 ^ (prefixWord ++ tailWord_5800405).sum := by decide
  have hdescent : baseEnd_5800405 < baseStart_5800405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5800405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5800415 : List Nat := [1, 1, 2, 3, 3, 2, 1, 4, 1, 2, 3]
def baseStart_5800415 : Nat := 118140960795 + 5800415 * 2 ^ 59
def prefixEnd_5800415 : Nat := 4983230072969 + 3 ^ 40 * 5800415 * 2
def baseEnd_5800415 : Nat := 2978400890549028583336883

theorem tailTrace_5800415 : CollatzResearch.WordTrace tailWord_5800415 prefixEnd_5800415 2978400890549028583336883 := by
  unfold tailWord_5800415
  simp only [CollatzResearch.WordTrace]
  refine ⟨211558515281094561858866699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141039010187396374572577799 211558515281094561858866699)
  ·
    refine ⟨317337772921641842788300049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211558515281094561858866699 317337772921641842788300049)
    ·
      refine ⟨238003329691231382091225037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317337772921641842788300049 238003329691231382091225037)
      ·
        refine ⟨89251248634211768284209389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238003329691231382091225037 89251248634211768284209389)
        ·
          refine ⟨33469218237829413106578521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89251248634211768284209389 33469218237829413106578521)
          ·
            refine ⟨25101913678372059829933891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33469218237829413106578521 25101913678372059829933891)
            ·
              refine ⟨37652870517558089744900837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25101913678372059829933891 37652870517558089744900837)
              ·
                refine ⟨7059913222042141827168907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37652870517558089744900837 7059913222042141827168907)
                ·
                  refine ⟨10589869833063212740753361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7059913222042141827168907 10589869833063212740753361)
                  ·
                    refine ⟨7942402374797409555565021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10589869833063212740753361 7942402374797409555565021)
                    ·
                      refine ⟨2978400890549028583336883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7942402374797409555565021 2978400890549028583336883)
                      ·
                        rfl

theorem cell23_5800415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 4, 1, 2, 3].length) (baseStart_5800415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5800415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5800415 prefixEnd_5800415 := by exact prefixLift 5800415
  have htrace : WordTrace (prefixWord ++ tailWord_5800415) baseStart_5800415 baseEnd_5800415 := by
    simpa [prefixWord, tailWord_5800415, baseEnd_5800415] using wordTrace_append hprefix tailTrace_5800415
  have hstable : (prefixWord ++ tailWord_5800415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5800415).length < 2 ^ (prefixWord ++ tailWord_5800415).sum := by decide
  have hdescent : baseEnd_5800415 < baseStart_5800415 := by decide
  rcases family_descends (prefixWord ++ tailWord_5800415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5800428 : List Nat := [2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 3]
def baseStart_5800428 : Nat := 118140960795 + 5800428 * 2 ^ 59
def prefixEnd_5800428 : Nat := 4983230072969 + 3 ^ 40 * 5800428 * 2
def baseEnd_5800428 : Nat := 2978407565797537032474323

theorem tailTrace_5800428 : CollatzResearch.WordTrace tailWord_5800428 prefixEnd_5800428 2978407565797537032474323 := by
  unfold tailWord_5800428
  simp only [CollatzResearch.WordTrace]
  refine ⟨105779494715023732539544969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141039326286698310052726625 105779494715023732539544969)
  ·
    refine ⟨79334621036267799404658727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105779494715023732539544969 79334621036267799404658727)
    ·
      refine ⟨119001931554401699106988091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79334621036267799404658727 119001931554401699106988091)
      ·
        refine ⟨178502897331602548660482137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119001931554401699106988091 178502897331602548660482137)
        ·
          refine ⟨133877172998701911495361603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178502897331602548660482137 133877172998701911495361603)
          ·
            refine ⟨200815759498052867243042405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133877172998701911495361603 200815759498052867243042405)
            ·
              refine ⟨37652954905884912608070451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 200815759498052867243042405 37652954905884912608070451)
              ·
                refine ⟨56479432358827368912105677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37652954905884912608070451 56479432358827368912105677)
                ·
                  refine ⟨21179787134560263342039629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56479432358827368912105677 21179787134560263342039629)
                  ·
                    refine ⟨7942420175460098753264861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21179787134560263342039629 7942420175460098753264861)
                    ·
                      refine ⟨2978407565797537032474323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7942420175460098753264861 2978407565797537032474323)
                      ·
                        rfl

theorem cell23_5800428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 3].length) (baseStart_5800428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5800428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5800428 prefixEnd_5800428 := by exact prefixLift 5800428
  have htrace : WordTrace (prefixWord ++ tailWord_5800428) baseStart_5800428 baseEnd_5800428 := by
    simpa [prefixWord, tailWord_5800428, baseEnd_5800428] using wordTrace_append hprefix tailTrace_5800428
  have hstable : (prefixWord ++ tailWord_5800428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5800428).length < 2 ^ (prefixWord ++ tailWord_5800428).sum := by decide
  have hdescent : baseEnd_5800428 < baseStart_5800428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5800428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5800431 : List Nat := [1, 1, 2, 1, 4, 1, 1, 2, 1, 9]
def baseStart_5800431 : Nat := 118140960795 + 5800431 * 2 ^ 59
def prefixEnd_5800431 : Nat := 4983230072969 + 3 ^ 40 * 5800431 * 2
def baseEnd_5800431 : Nat := 992803035413166840245603

theorem tailTrace_5800431 : CollatzResearch.WordTrace tailWord_5800431 prefixEnd_5800431 992803035413166840245603 := by
  unfold tailWord_5800431
  simp only [CollatzResearch.WordTrace]
  refine ⟨211559098849036596591449147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141039399232691064394299431 211559098849036596591449147)
  ·
    refine ⟨317338648273554894887173721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211559098849036596591449147 317338648273554894887173721)
    ·
      refine ⟨238003986205166171165380291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317338648273554894887173721 238003986205166171165380291)
      ·
        refine ⟨357005979307749256748070437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238003986205166171165380291 357005979307749256748070437)
        ·
          refine ⟨66938621120202985640263207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 357005979307749256748070437 66938621120202985640263207)
          ·
            refine ⟨100407931680304478460394811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66938621120202985640263207 100407931680304478460394811)
            ·
              refine ⟨150611897520456717690592217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100407931680304478460394811 150611897520456717690592217)
              ·
                refine ⟨112958923140342538267944163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150611897520456717690592217 112958923140342538267944163)
                ·
                  refine ⟨169438384710513807401916245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112958923140342538267944163 169438384710513807401916245)
                  ·
                    refine ⟨992803035413166840245603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 169438384710513807401916245 992803035413166840245603)
                    ·
                      rfl

theorem cell23_5800431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 9].length) (baseStart_5800431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5800431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5800431 prefixEnd_5800431 := by exact prefixLift 5800431
  have htrace : WordTrace (prefixWord ++ tailWord_5800431) baseStart_5800431 baseEnd_5800431 := by
    simpa [prefixWord, tailWord_5800431, baseEnd_5800431] using wordTrace_append hprefix tailTrace_5800431
  have hstable : (prefixWord ++ tailWord_5800431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5800431).length < 2 ^ (prefixWord ++ tailWord_5800431).sum := by decide
  have hdescent : baseEnd_5800431 < baseStart_5800431 := by decide
  rcases family_descends (prefixWord ++ tailWord_5800431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5800445 : List Nat := [1, 4, 1, 1, 1, 3, 1, 3, 4, 1, 3]
def baseStart_5800445 : Nat := 118140960795 + 5800445 * 2 ^ 59
def prefixEnd_5800445 : Nat := 4983230072969 + 3 ^ 40 * 5800445 * 2
def baseEnd_5800445 : Nat := 2978416294968663465961745

theorem tailTrace_5800445 : CollatzResearch.WordTrace tailWord_5800445 prefixEnd_5800445 2978416294968663465961745 := by
  unfold tailWord_5800445
  simp only [CollatzResearch.WordTrace]
  refine ⟨211559609470985876982458789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141039739647323917988305859 211559609470985876982458789)
  ·
    refine ⟨39667426775809851934211023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 211559609470985876982458789 39667426775809851934211023)
    ·
      refine ⟨59501140163714777901316535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39667426775809851934211023 59501140163714777901316535)
      ·
        refine ⟨89251710245572166851974803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59501140163714777901316535 89251710245572166851974803)
        ·
          refine ⟨133877565368358250277962205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89251710245572166851974803 133877565368358250277962205)
          ·
            refine ⟨50204087013134343854235827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133877565368358250277962205 50204087013134343854235827)
            ·
              refine ⟨75306130519701515781353741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50204087013134343854235827 75306130519701515781353741)
              ·
                refine ⟨28239798944888068418007653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75306130519701515781353741 28239798944888068418007653)
                ·
                  refine ⟨5294962302166512828376435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28239798944888068418007653 5294962302166512828376435)
                  ·
                    refine ⟨7942443453249769242564653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5294962302166512828376435 7942443453249769242564653)
                    ·
                      refine ⟨2978416294968663465961745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7942443453249769242564653 2978416294968663465961745)
                      ·
                        rfl

theorem cell23_5800445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 4, 1, 3].length) (baseStart_5800445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5800445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5800445 prefixEnd_5800445 := by exact prefixLift 5800445
  have htrace : WordTrace (prefixWord ++ tailWord_5800445) baseStart_5800445 baseEnd_5800445 := by
    simpa [prefixWord, tailWord_5800445, baseEnd_5800445] using wordTrace_append hprefix tailTrace_5800445
  have hstable : (prefixWord ++ tailWord_5800445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5800445).length < 2 ^ (prefixWord ++ tailWord_5800445).sum := by decide
  have hdescent : baseEnd_5800445 < baseStart_5800445 := by decide
  rcases family_descends (prefixWord ++ tailWord_5800445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5800472 : List Nat := [2, 1, 2, 3, 3, 2, 1, 1, 3, 3, 2]
def baseStart_5800472 : Nat := 118140960795 + 5800472 * 2 ^ 59
def prefixEnd_5800472 : Nat := 4983230072969 + 3 ^ 40 * 5800472 * 2
def baseEnd_5800472 : Nat := 2978430158946334860324121

theorem tailTrace_5800472 : CollatzResearch.WordTrace tailWord_5800472 prefixEnd_5800472 2978430158946334860324121 := by
  unfold tailWord_5800472
  simp only [CollatzResearch.WordTrace]
  refine ⟨105780297120944030296845835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141040396161258707062461113 105780297120944030296845835)
  ·
    refine ⟨158670445681416045445268753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105780297120944030296845835 158670445681416045445268753)
    ·
      refine ⟨119002834261062034083951565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158670445681416045445268753 119002834261062034083951565)
      ·
        refine ⟨44626062847898262781481837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119002834261062034083951565 44626062847898262781481837)
        ·
          refine ⟨16734773567961848543055689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44626062847898262781481837 16734773567961848543055689)
          ·
            refine ⟨12551080175971386407291767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16734773567961848543055689 12551080175971386407291767)
            ·
              refine ⟨18826620263957079610937651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12551080175971386407291767 18826620263957079610937651)
              ·
                refine ⟨28239930395935619416406477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18826620263957079610937651 28239930395935619416406477)
                ·
                  refine ⟨10589973898475857281152429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28239930395935619416406477 10589973898475857281152429)
                  ·
                    refine ⟨3971240211928446480432161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10589973898475857281152429 3971240211928446480432161)
                    ·
                      refine ⟨2978430158946334860324121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3971240211928446480432161 2978430158946334860324121)
                      ·
                        rfl

theorem cell23_5800472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 3, 3, 2].length) (baseStart_5800472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5800472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5800472 prefixEnd_5800472 := by exact prefixLift 5800472
  have htrace : WordTrace (prefixWord ++ tailWord_5800472) baseStart_5800472 baseEnd_5800472 := by
    simpa [prefixWord, tailWord_5800472, baseEnd_5800472] using wordTrace_append hprefix tailTrace_5800472
  have hstable : (prefixWord ++ tailWord_5800472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5800472).length < 2 ^ (prefixWord ++ tailWord_5800472).sum := by decide
  have hdescent : baseEnd_5800472 < baseStart_5800472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5800472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5800485 : List Nat := [1, 3, 1, 2, 2, 1, 3, 1, 3, 4, 2]
def baseStart_5800485 : Nat := 118140960795 + 5800485 * 2 ^ 59
def prefixEnd_5800485 : Nat := 4983230072969 + 3 ^ 40 * 5800485 * 2
def baseEnd_5800485 : Nat := 2978436834194843309461561

theorem tailTrace_5800485 : CollatzResearch.WordTrace tailWord_5800485 prefixEnd_5800485 2978436834194843309461561 := by
  unfold tailWord_5800485
  simp only [CollatzResearch.WordTrace]
  refine ⟨211561068390840963813914909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141040712260560642542609939 211561068390840963813914909)
  ·
    refine ⟨79335400646565361430218091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211561068390840963813914909 79335400646565361430218091)
    ·
      refine ⟨119003100969848042145327137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79335400646565361430218091 119003100969848042145327137)
      ·
        refine ⟨89252325727386031608995353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119003100969848042145327137 89252325727386031608995353)
        ·
          refine ⟨66939244295539523706746515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89252325727386031608995353 66939244295539523706746515)
          ·
            refine ⟨100408866443309285560119773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66939244295539523706746515 100408866443309285560119773)
            ·
              refine ⟨37653324916240982085044915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100408866443309285560119773 37653324916240982085044915)
              ·
                refine ⟨56479987374361473127567373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37653324916240982085044915 56479987374361473127567373)
                ·
                  refine ⟨21179995265385552422837765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56479987374361473127567373 21179995265385552422837765)
                  ·
                    refine ⟨3971249112259791079282081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21179995265385552422837765 3971249112259791079282081)
                    ·
                      refine ⟨2978436834194843309461561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3971249112259791079282081 2978436834194843309461561)
                      ·
                        rfl

theorem cell23_5800485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 4, 2].length) (baseStart_5800485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5800485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5800485 prefixEnd_5800485 := by exact prefixLift 5800485
  have htrace : WordTrace (prefixWord ++ tailWord_5800485) baseStart_5800485 baseEnd_5800485 := by
    simpa [prefixWord, tailWord_5800485, baseEnd_5800485] using wordTrace_append hprefix tailTrace_5800485
  have hstable : (prefixWord ++ tailWord_5800485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5800485).length < 2 ^ (prefixWord ++ tailWord_5800485).sum := by decide
  have hdescent : baseEnd_5800485 < baseStart_5800485 := by decide
  rcases family_descends (prefixWord ++ tailWord_5800485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5800519 : List Nat := [1, 1, 4, 1, 4, 1, 2, 3, 2, 2, 2]
def baseStart_5800519 : Nat := 118140960795 + 5800519 * 2 ^ 59
def prefixEnd_5800519 : Nat := 4983230072969 + 3 ^ 40 * 5800519 * 2
def baseEnd_5800519 : Nat := 2978454292537096176436405

theorem tailTrace_5800519 : CollatzResearch.WordTrace tailWord_5800519 prefixEnd_5800519 2978454292537096176436405 := by
  unfold tailWord_5800519
  simp only [CollatzResearch.WordTrace]
  refine ⟨211562308472717787620652611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141041538981811858413768407 211562308472717787620652611)
  ·
    refine ⟨317343462709076681430978917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211562308472717787620652611 317343462709076681430978917)
    ·
      refine ⟨59501899257951877768308547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 317343462709076681430978917 59501899257951877768308547)
      ·
        refine ⟨89252848886927816652462821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59501899257951877768308547 89252848886927816652462821)
        ·
          refine ⟨16734909166298965622336779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89252848886927816652462821 16734909166298965622336779)
          ·
            refine ⟨25102363749448448433505169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16734909166298965622336779 25102363749448448433505169)
            ·
              refine ⟨18826772812086336325128877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25102363749448448433505169 18826772812086336325128877)
              ·
                refine ⟨7060039804532376121923329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18826772812086336325128877 7060039804532376121923329)
                ·
                  refine ⟨5295029853399282091442497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7060039804532376121923329 5295029853399282091442497)
                  ·
                    refine ⟨3971272390049461568581873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5295029853399282091442497 3971272390049461568581873)
                    ·
                      refine ⟨2978454292537096176436405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3971272390049461568581873 2978454292537096176436405)
                      ·
                        rfl

theorem cell23_5800519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 3, 2, 2, 2].length) (baseStart_5800519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5800519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5800519 prefixEnd_5800519 := by exact prefixLift 5800519
  have htrace : WordTrace (prefixWord ++ tailWord_5800519) baseStart_5800519 baseEnd_5800519 := by
    simpa [prefixWord, tailWord_5800519, baseEnd_5800519] using wordTrace_append hprefix tailTrace_5800519
  have hstable : (prefixWord ++ tailWord_5800519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5800519).length < 2 ^ (prefixWord ++ tailWord_5800519).sum := by decide
  have hdescent : baseEnd_5800519 < baseStart_5800519 := by decide
  rcases family_descends (prefixWord ++ tailWord_5800519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5800525 : List Nat := [1, 6, 1, 1, 2, 1, 1, 1, 9]
def baseStart_5800525 : Nat := 118140960795 + 5800525 * 2 ^ 59
def prefixEnd_5800525 : Nat := 4983230072969 + 3 ^ 40 * 5800525 * 2
def baseEnd_5800525 : Nat := 330939708157891461440153

theorem tailTrace_5800525 : CollatzResearch.WordTrace tailWord_5800525 prefixEnd_5800525 330939708157891461440153 := by
  unfold tailWord_5800525
  simp only [CollatzResearch.WordTrace]
  refine ⟨211562527310696050645371029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141041684873797367096914019 211562527310696050645371029)
  ·
    refine ⟨9916993467688877374001767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 211562527310696050645371029 9916993467688877374001767)
    ·
      refine ⟨14875490201533316061002651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9916993467688877374001767 14875490201533316061002651)
      ·
        refine ⟨22313235302299974091503977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14875490201533316061002651 22313235302299974091503977)
        ·
          refine ⟨16734926476724980568627983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22313235302299974091503977 16734926476724980568627983)
          ·
            refine ⟨25102389715087470852941975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16734926476724980568627983 25102389715087470852941975)
            ·
              refine ⟨37653584572631206279412963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25102389715087470852941975 37653584572631206279412963)
              ·
                refine ⟨56480376858946809419119445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37653584572631206279412963 56480376858946809419119445)
                ·
                  refine ⟨330939708157891461440153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 56480376858946809419119445 330939708157891461440153)
                  ·
                    rfl

theorem cell23_5800525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_5800525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5800525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5800525 prefixEnd_5800525 := by exact prefixLift 5800525
  have htrace : WordTrace (prefixWord ++ tailWord_5800525) baseStart_5800525 baseEnd_5800525 := by
    simpa [prefixWord, tailWord_5800525, baseEnd_5800525] using wordTrace_append hprefix tailTrace_5800525
  have hstable : (prefixWord ++ tailWord_5800525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5800525).length < 2 ^ (prefixWord ++ tailWord_5800525).sum := by decide
  have hdescent : baseEnd_5800525 < baseStart_5800525 := by decide
  rcases family_descends (prefixWord ++ tailWord_5800525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5800575 : List Nat := [1, 1, 2, 2, 1, 1, 1, 5, 1, 6, 2]
def baseStart_5800575 : Nat := 118140960795 + 5800575 * 2 ^ 59
def prefixEnd_5800575 : Nat := 4983230072969 + 3 ^ 40 * 5800575 * 2
def baseEnd_5800575 : Nat := 2978483047453747957336147

theorem tailTrace_5800575 : CollatzResearch.WordTrace tailWord_5800575 prefixEnd_5800575 2978483047453747957336147 := by
  unfold tailWord_5800575
  simp only [CollatzResearch.WordTrace]
  refine ⟨211564350960514909184691179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141042900640343272789794119 211564350960514909184691179)
  ·
    refine ⟨317346526440772363777036769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211564350960514909184691179 317346526440772363777036769)
    ·
      refine ⟨238009894830579272832777577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317346526440772363777036769 238009894830579272832777577)
      ·
        refine ⟨178507421122934454624583183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238009894830579272832777577 178507421122934454624583183)
        ·
          refine ⟨267761131684401681936874775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178507421122934454624583183 267761131684401681936874775)
          ·
            refine ⟨401641697526602522905312163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267761131684401681936874775 401641697526602522905312163)
            ·
              refine ⟨602462546289903784357968245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 401641697526602522905312163 602462546289903784357968245)
              ·
                refine ⟨56480863714678479783559523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 602462546289903784357968245 56480863714678479783559523)
                ·
                  refine ⟨84721295572017719675339285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56480863714678479783559523 84721295572017719675339285)
                  ·
                    refine ⟨3971310729938330609781529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 84721295572017719675339285 3971310729938330609781529)
                    ·
                      refine ⟨2978483047453747957336147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3971310729938330609781529 2978483047453747957336147)
                      ·
                        rfl

theorem cell23_5800575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 6, 2].length) (baseStart_5800575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5800575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5800575 prefixEnd_5800575 := by exact prefixLift 5800575
  have htrace : WordTrace (prefixWord ++ tailWord_5800575) baseStart_5800575 baseEnd_5800575 := by
    simpa [prefixWord, tailWord_5800575, baseEnd_5800575] using wordTrace_append hprefix tailTrace_5800575
  have hstable : (prefixWord ++ tailWord_5800575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5800575).length < 2 ^ (prefixWord ++ tailWord_5800575).sum := by decide
  have hdescent : baseEnd_5800575 < baseStart_5800575 := by decide
  rcases family_descends (prefixWord ++ tailWord_5800575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5800588 : List Nat := [2, 2, 1, 2, 1, 1, 2, 2, 1, 3, 6]
def baseStart_5800588 : Nat := 118140960795 + 5800588 * 2 ^ 59
def prefixEnd_5800588 : Nat := 4983230072969 + 3 ^ 40 * 5800588 * 2
def baseEnd_5800588 : Nat := 2978489722702256406473587

theorem tailTrace_5800588 : CollatzResearch.WordTrace tailWord_5800588 prefixEnd_5800588 2978489722702256406473587 := by
  unfold tailWord_5800588
  simp only [CollatzResearch.WordTrace]
  refine ⟨105782412554733906202457209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141043216739645208269942945 105782412554733906202457209)
  ·
    refine ⟨79336809416050429651842907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105782412554733906202457209 79336809416050429651842907)
    ·
      refine ⟨119005214124075644477764361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79336809416050429651842907 119005214124075644477764361)
      ·
        refine ⟨89253910593056733358323271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119005214124075644477764361 89253910593056733358323271)
        ·
          refine ⟨133880865889585100037484907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89253910593056733358323271 133880865889585100037484907)
          ·
            refine ⟨200821298834377650056227361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133880865889585100037484907 200821298834377650056227361)
            ·
              refine ⟨150615974125783237542170521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200821298834377650056227361 150615974125783237542170521)
              ·
                refine ⟨112961980594337428156627891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150615974125783237542170521 112961980594337428156627891)
                ·
                  refine ⟨169442970891506142234941837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112961980594337428156627891 169442970891506142234941837)
                  ·
                    refine ⟨63541114084314803338103189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 169442970891506142234941837 63541114084314803338103189)
                    ·
                      refine ⟨2978489722702256406473587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63541114084314803338103189 2978489722702256406473587)
                      ·
                        rfl

theorem cell23_5800588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_5800588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5800588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5800588 prefixEnd_5800588 := by exact prefixLift 5800588
  have htrace : WordTrace (prefixWord ++ tailWord_5800588) baseStart_5800588 baseEnd_5800588 := by
    simpa [prefixWord, tailWord_5800588, baseEnd_5800588] using wordTrace_append hprefix tailTrace_5800588
  have hstable : (prefixWord ++ tailWord_5800588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5800588).length < 2 ^ (prefixWord ++ tailWord_5800588).sum := by decide
  have hdescent : baseEnd_5800588 < baseStart_5800588 := by decide
  rcases family_descends (prefixWord ++ tailWord_5800588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5800612 : List Nat := [2, 3, 1, 2, 2, 1, 3, 2, 2, 2, 3]
def baseStart_5800612 : Nat := 118140960795 + 5800612 * 2 ^ 59
def prefixEnd_5800612 : Nat := 4983230072969 + 3 ^ 40 * 5800612 * 2
def baseEnd_5800612 : Nat := 2978502046237964312573477

theorem tailTrace_5800612 : CollatzResearch.WordTrace tailWord_5800612 prefixEnd_5800612 2978502046237964312573477 := by
  unfold tailWord_5800612
  simp only [CollatzResearch.WordTrace]
  refine ⟨105782850230690432251894045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141043800307587243002525393 105782850230690432251894045)
  ·
    refine ⟨39668568836508912094460267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105782850230690432251894045 39668568836508912094460267)
    ·
      refine ⟨59502853254763368141690401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39668568836508912094460267 59502853254763368141690401)
      ·
        refine ⟨44627139941072526106267801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59502853254763368141690401 44627139941072526106267801)
        ·
          refine ⟨33470354955804394579700851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44627139941072526106267801 33470354955804394579700851)
          ·
            refine ⟨50205532433706591869551277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33470354955804394579700851 50205532433706591869551277)
            ·
              refine ⟨18827074662639971951081729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50205532433706591869551277 18827074662639971951081729)
              ·
                refine ⟨14120305996979978963311297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18827074662639971951081729 14120305996979978963311297)
                ·
                  refine ⟨10590229497734984222483473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14120305996979978963311297 10590229497734984222483473)
                  ·
                    refine ⟨7942672123301238166862605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10590229497734984222483473 7942672123301238166862605)
                    ·
                      refine ⟨2978502046237964312573477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7942672123301238166862605 2978502046237964312573477)
                      ·
                        rfl

theorem cell23_5800612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_5800612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5800612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5800612 prefixEnd_5800612 := by exact prefixLift 5800612
  have htrace : WordTrace (prefixWord ++ tailWord_5800612) baseStart_5800612 baseEnd_5800612 := by
    simpa [prefixWord, tailWord_5800612, baseEnd_5800612] using wordTrace_append hprefix tailTrace_5800612
  have hstable : (prefixWord ++ tailWord_5800612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5800612).length < 2 ^ (prefixWord ++ tailWord_5800612).sum := by decide
  have hdescent : baseEnd_5800612 < baseStart_5800612 := by decide
  rcases family_descends (prefixWord ++ tailWord_5800612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5800676 : List Nat := [2, 3, 1, 1, 1, 5, 1, 4, 1, 1, 3]
def baseStart_5800676 : Nat := 118140960795 + 5800676 * 2 ^ 59
def prefixEnd_5800676 : Nat := 4983230072969 + 3 ^ 40 * 5800676 * 2
def baseEnd_5800676 : Nat := 2978534908999852062173183

theorem tailTrace_5800676 : CollatzResearch.WordTrace tailWord_5800676 prefixEnd_5800676 2978534908999852062173183 := by
  unfold tailWord_5800676
  simp only [CollatzResearch.WordTrace]
  refine ⟨105784017366574501717058941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141045356488766002289411921 105784017366574501717058941)
  ·
    refine ⟨39669006512465438143897103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105784017366574501717058941 39669006512465438143897103)
    ·
      refine ⟨59503509768698157215845655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39669006512465438143897103 59503509768698157215845655)
      ·
        refine ⟨89255264653047235823768483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59503509768698157215845655 89255264653047235823768483)
        ·
          refine ⟨133882896979570853735652725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89255264653047235823768483 133882896979570853735652725)
          ·
            refine ⟨12551521591834767537717443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 133882896979570853735652725 12551521591834767537717443)
            ·
              refine ⟨18827282387752151306576165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12551521591834767537717443 18827282387752151306576165)
              ·
                refine ⟨3530115447703528369983031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18827282387752151306576165 3530115447703528369983031)
                ·
                  refine ⟨5295173171555292554974547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3530115447703528369983031 5295173171555292554974547)
                  ·
                    refine ⟨7942759757332938832461821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5295173171555292554974547 7942759757332938832461821)
                    ·
                      refine ⟨2978534908999852062173183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7942759757332938832461821 2978534908999852062173183)
                      ·
                        rfl

theorem cell23_5800676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 4, 1, 1, 3].length) (baseStart_5800676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5800676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5800676 prefixEnd_5800676 := by exact prefixLift 5800676
  have htrace : WordTrace (prefixWord ++ tailWord_5800676) baseStart_5800676 baseEnd_5800676 := by
    simpa [prefixWord, tailWord_5800676, baseEnd_5800676] using wordTrace_append hprefix tailTrace_5800676
  have hstable : (prefixWord ++ tailWord_5800676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5800676).length < 2 ^ (prefixWord ++ tailWord_5800676).sum := by decide
  have hdescent : baseEnd_5800676 < baseStart_5800676 := by decide
  rcases family_descends (prefixWord ++ tailWord_5800676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5800682 : List Nat := [3, 1, 3, 1, 1, 1, 1, 2, 2, 6, 2]
def baseStart_5800682 : Nat := 118140960795 + 5800682 * 2 ^ 59
def prefixEnd_5800682 : Nat := 4983230072969 + 3 ^ 40 * 5800682 * 2
def baseEnd_5800682 : Nat := 2978537989883779038698155

theorem tailTrace_5800682 : CollatzResearch.WordTrace tailWord_5800682 prefixEnd_5800682 2978537989883779038698155 := by
  unfold tailWord_5800682
  simp only [CollatzResearch.WordTrace]
  refine ⟨52892063392781816614709075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141045502380751510972557533 52892063392781816614709075)
  ·
    refine ⟨79338095089172724922063613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52892063392781816614709075 79338095089172724922063613)
    ·
      refine ⟨29751785658439771845773855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79338095089172724922063613 29751785658439771845773855)
      ·
        refine ⟨44627678487659657768660783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29751785658439771845773855 44627678487659657768660783)
        ·
          refine ⟨66941517731489486652991175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44627678487659657768660783 66941517731489486652991175)
          ·
            refine ⟨100412276597234229979486763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66941517731489486652991175 100412276597234229979486763)
            ·
              refine ⟨150618414895851344969230145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100412276597234229979486763 150618414895851344969230145)
              ·
                refine ⟨112963811171888508726922609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150618414895851344969230145 112963811171888508726922609)
                ·
                  refine ⟨84722858378916381545191957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112963811171888508726922609 84722858378916381545191957)
                  ·
                    refine ⟨3971383986511705384930873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 84722858378916381545191957 3971383986511705384930873)
                    ·
                      refine ⟨2978537989883779038698155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3971383986511705384930873 2978537989883779038698155)
                      ·
                        rfl

theorem cell23_5800682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 2, 6, 2].length) (baseStart_5800682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5800682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5800682 prefixEnd_5800682 := by exact prefixLift 5800682
  have htrace : WordTrace (prefixWord ++ tailWord_5800682) baseStart_5800682 baseEnd_5800682 := by
    simpa [prefixWord, tailWord_5800682, baseEnd_5800682] using wordTrace_append hprefix tailTrace_5800682
  have hstable : (prefixWord ++ tailWord_5800682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5800682).length < 2 ^ (prefixWord ++ tailWord_5800682).sum := by decide
  have hdescent : baseEnd_5800682 < baseStart_5800682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5800682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5800712 : List Nat := [2, 1, 3, 2, 2, 2, 2, 2, 1, 2, 4]
def baseStart_5800712 : Nat := 118140960795 + 5800712 * 2 ^ 59
def prefixEnd_5800712 : Nat := 4983230072969 + 3 ^ 40 * 5800712 * 2
def baseEnd_5800712 : Nat := 2978553394303413921323017

theorem tailTrace_5800712 : CollatzResearch.WordTrace tailWord_5800712 prefixEnd_5800712 2978553394303413921323017 := by
  unfold tailWord_5800712
  simp only [CollatzResearch.WordTrace]
  refine ⟨105784673880509290791214195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141046231840679054388285593 105784673880509290791214195)
  ·
    refine ⟨158677010820763936186821293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105784673880509290791214195 158677010820763936186821293)
    ·
      refine ⟨59503879057786476070057985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158677010820763936186821293 59503879057786476070057985)
      ·
        refine ⟨44627909293339857052543489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59503879057786476070057985 44627909293339857052543489)
        ·
          refine ⟨33470931970004892789407617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44627909293339857052543489 33470931970004892789407617)
          ·
            refine ⟨25103198977503669592055713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33470931970004892789407617 25103198977503669592055713)
            ·
              refine ⟨18827399233127752194041785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25103198977503669592055713 18827399233127752194041785)
              ·
                refine ⟨14120549424845814145531339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18827399233127752194041785 14120549424845814145531339)
                ·
                  refine ⟨21180824137268721218297009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14120549424845814145531339 21180824137268721218297009)
                  ·
                    refine ⟨15885618102951540913722757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21180824137268721218297009 15885618102951540913722757)
                    ·
                      refine ⟨2978553394303413921323017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15885618102951540913722757 2978553394303413921323017)
                      ·
                        rfl

theorem cell23_5800712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_5800712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5800712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5800712 prefixEnd_5800712 := by exact prefixLift 5800712
  have htrace : WordTrace (prefixWord ++ tailWord_5800712) baseStart_5800712 baseEnd_5800712 := by
    simpa [prefixWord, tailWord_5800712, baseEnd_5800712] using wordTrace_append hprefix tailTrace_5800712
  have hstable : (prefixWord ++ tailWord_5800712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5800712).length < 2 ^ (prefixWord ++ tailWord_5800712).sum := by decide
  have hdescent : baseEnd_5800712 < baseStart_5800712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5800712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5800756 : List Nat := [2, 5, 1, 1, 3, 2, 2, 7]
def baseStart_5800756 : Nat := 118140960795 + 5800756 * 2 ^ 59
def prefixEnd_5800756 : Nat := 4983230072969 + 3 ^ 40 * 5800756 * 2
def baseEnd_5800756 : Nat := 110317629164896731450845

theorem tailTrace_5800756 : CollatzResearch.WordTrace tailWord_5800756 prefixEnd_5800756 110317629164896731450845 := by
  unfold tailWord_5800756
  simp only [CollatzResearch.WordTrace]
  refine ⟨105785476286429588548515061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141047301715239451398020081 105785476286429588548515061)
  ·
    refine ⟨9917388401852773926423287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 105785476286429588548515061 9917388401852773926423287)
    ·
      refine ⟨14876082602779160889634931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9917388401852773926423287 14876082602779160889634931)
      ·
        refine ⟨22314123904168741334452397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14876082602779160889634931 22314123904168741334452397)
        ·
          refine ⟨8367796464063278000419649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22314123904168741334452397 8367796464063278000419649)
          ·
            refine ⟨6275847348047458500314737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8367796464063278000419649 6275847348047458500314737)
            ·
              refine ⟨4706885511035593875236053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6275847348047458500314737 4706885511035593875236053)
              ·
                refine ⟨110317629164896731450845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4706885511035593875236053 110317629164896731450845)
                ·
                  rfl

theorem cell23_5800756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 7].length) (baseStart_5800756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5800756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5800756 prefixEnd_5800756 := by exact prefixLift 5800756
  have htrace : WordTrace (prefixWord ++ tailWord_5800756) baseStart_5800756 baseEnd_5800756 := by
    simpa [prefixWord, tailWord_5800756, baseEnd_5800756] using wordTrace_append hprefix tailTrace_5800756
  have hstable : (prefixWord ++ tailWord_5800756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5800756).length < 2 ^ (prefixWord ++ tailWord_5800756).sum := by decide
  have hdescent : baseEnd_5800756 < baseStart_5800756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5800756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5800815 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 8]
def baseStart_5800815 : Nat := 118140960795 + 5800815 * 2 ^ 59
def prefixEnd_5800815 : Nat := 4983230072969 + 3 ^ 40 * 5800815 * 2
def baseEnd_5800815 : Nat := 2978606282810827018335043

theorem tailTrace_5800815 : CollatzResearch.WordTrace tailWord_5800815 prefixEnd_5800815 2978606282810827018335043 := by
  unfold tailWord_5800815
  simp only [CollatzResearch.WordTrace]
  refine ⟨211573104479645430173427899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141048736319763620115618599 211573104479645430173427899)
  ·
    refine ⟨317359656719468145260141849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211573104479645430173427899 317359656719468145260141849)
    ·
      refine ⟨238019742539601108945106387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317359656719468145260141849 238019742539601108945106387)
      ·
        refine ⟨357029613809401663417659581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238019742539601108945106387 357029613809401663417659581)
        ·
          refine ⟨133886105178525623781622343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 357029613809401663417659581 133886105178525623781622343)
          ·
            refine ⟨200829157767788435672433515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133886105178525623781622343 200829157767788435672433515)
            ·
              refine ⟨301243736651682653508650273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200829157767788435672433515 301243736651682653508650273)
              ·
                refine ⟨225932802488761990131487705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 301243736651682653508650273 225932802488761990131487705)
                ·
                  refine ⟨169449601866571492598615779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 225932802488761990131487705 169449601866571492598615779)
                  ·
                    refine ⟨254174402799857238897923669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 169449601866571492598615779 254174402799857238897923669)
                    ·
                      refine ⟨2978606282810827018335043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 254174402799857238897923669 2978606282810827018335043)
                      ·
                        rfl

theorem cell23_5800815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 8].length) (baseStart_5800815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5800815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5800815 prefixEnd_5800815 := by exact prefixLift 5800815
  have htrace : WordTrace (prefixWord ++ tailWord_5800815) baseStart_5800815 baseEnd_5800815 := by
    simpa [prefixWord, tailWord_5800815, baseEnd_5800815] using wordTrace_append hprefix tailTrace_5800815
  have hstable : (prefixWord ++ tailWord_5800815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5800815).length < 2 ^ (prefixWord ++ tailWord_5800815).sum := by decide
  have hdescent : baseEnd_5800815 < baseStart_5800815 := by decide
  rcases family_descends (prefixWord ++ tailWord_5800815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5800956 : List Nat := [2, 2, 2, 1, 2, 3, 1, 1, 4, 3, 2]
def baseStart_5800956 : Nat := 118140960795 + 5800956 * 2 ^ 59
def prefixEnd_5800956 : Nat := 4983230072969 + 3 ^ 40 * 5800956 * 2
def baseEnd_5800956 : Nat := 2978678683583110966671895

theorem tailTrace_5800956 : CollatzResearch.WordTrace tailWord_5800956 prefixEnd_5800956 2978678683583110966671895 := by
  unfold tailWord_5800956
  simp only [CollatzResearch.WordTrace]
  refine ⟨105789123586067305627155361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141052164781423074169540481 105789123586067305627155361)
  ·
    refine ⟨79341842689550479220366521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105789123586067305627155361 79341842689550479220366521)
    ·
      refine ⟨59506382017162859415274891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79341842689550479220366521 59506382017162859415274891)
      ·
        refine ⟨89259573025744289122912337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59506382017162859415274891 89259573025744289122912337)
        ·
          refine ⟨66944679769308216842184253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89259573025744289122912337 66944679769308216842184253)
          ·
            refine ⟨25104254913490581315819095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66944679769308216842184253 25104254913490581315819095)
            ·
              refine ⟨37656382370235871973728643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25104254913490581315819095 37656382370235871973728643)
              ·
                refine ⟨56484573555353807960592965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37656382370235871973728643 56484573555353807960592965)
                ·
                  refine ⟨10590857541628838992611181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56484573555353807960592965 10590857541628838992611181)
                  ·
                    refine ⟨3971571578110814622229193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10590857541628838992611181 3971571578110814622229193)
                    ·
                      refine ⟨2978678683583110966671895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3971571578110814622229193 2978678683583110966671895)
                      ·
                        rfl

theorem cell23_5800956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 4, 3, 2].length) (baseStart_5800956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5800956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5800956 prefixEnd_5800956 := by exact prefixLift 5800956
  have htrace : WordTrace (prefixWord ++ tailWord_5800956) baseStart_5800956 baseEnd_5800956 := by
    simpa [prefixWord, tailWord_5800956, baseEnd_5800956] using wordTrace_append hprefix tailTrace_5800956
  have hstable : (prefixWord ++ tailWord_5800956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5800956).length < 2 ^ (prefixWord ++ tailWord_5800956).sum := by decide
  have hdescent : baseEnd_5800956 < baseStart_5800956 := by decide
  rcases family_descends (prefixWord ++ tailWord_5800956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5800983 : List Nat := [1, 1, 3, 5, 1, 3, 1, 2, 1, 5]
def baseStart_5800983 : Nat := 118140960795 + 5800983 * 2 ^ 59
def prefixEnd_5800983 : Nat := 4983230072969 + 3 ^ 40 * 5800983 * 2
def baseEnd_5800983 : Nat := 992897515853594120344757

theorem tailTrace_5800983 : CollatzResearch.WordTrace tailWord_5800983 prefixEnd_5800983 992897515853594120344757 := by
  unfold tailWord_5800983
  simp only [CollatzResearch.WordTrace]
  refine ⟨211579231943036794865543603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141052821295357863243695735 211579231943036794865543603)
  ·
    refine ⟨317368847914555192298315405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211579231943036794865543603 317368847914555192298315405)
    ·
      refine ⟨119013317967958197111868277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 317368847914555192298315405 119013317967958197111868277)
      ·
        refine ⟨11157498559496080979237651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 119013317967958197111868277 11157498559496080979237651)
        ·
          refine ⟨16736247839244121468856477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11157498559496080979237651 16736247839244121468856477)
          ·
            refine ⟨6276092939716545550821179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16736247839244121468856477 6276092939716545550821179)
            ·
              refine ⟨9414139409574818326231769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6276092939716545550821179 9414139409574818326231769)
              ·
                refine ⟨7060604557181113744673827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9414139409574818326231769 7060604557181113744673827)
                ·
                  refine ⟨10590906835771670617010741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7060604557181113744673827 10590906835771670617010741)
                  ·
                    refine ⟨992897515853594120344757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10590906835771670617010741 992897515853594120344757)
                    ·
                      rfl

theorem cell23_5800983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 2, 1, 5].length) (baseStart_5800983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5800983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5800983 prefixEnd_5800983 := by exact prefixLift 5800983
  have htrace : WordTrace (prefixWord ++ tailWord_5800983) baseStart_5800983 baseEnd_5800983 := by
    simpa [prefixWord, tailWord_5800983, baseEnd_5800983] using wordTrace_append hprefix tailTrace_5800983
  have hstable : (prefixWord ++ tailWord_5800983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5800983).length < 2 ^ (prefixWord ++ tailWord_5800983).sum := by decide
  have hdescent : baseEnd_5800983 < baseStart_5800983 := by decide
  rcases family_descends (prefixWord ++ tailWord_5800983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5800996 : List Nat := [2, 3, 1, 4, 1, 2, 1, 2, 1, 6]
def baseStart_5800996 : Nat := 118140960795 + 5800996 * 2 ^ 59
def prefixEnd_5800996 : Nat := 4983230072969 + 3 ^ 40 * 5800996 * 2
def baseEnd_5800996 : Nat := 992899740936430270057237

theorem tailTrace_5800996 : CollatzResearch.WordTrace tailWord_5800996 prefixEnd_5800996 992899740936430270057237 := by
  unfold tailWord_5800996
  simp only [CollatzResearch.WordTrace]
  refine ⟨105789853045994849042883421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141053137394659798723844561 105789853045994849042883421)
  ·
    refine ⟨39671194892248068391081283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105789853045994849042883421 39671194892248068391081283)
    ·
      refine ⟨59506792338372102586621925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39671194892248068391081283 59506792338372102586621925)
      ·
        refine ⟨11157523563444769234991611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59506792338372102586621925 11157523563444769234991611)
        ·
          refine ⟨16736285345167153852487417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11157523563444769234991611 16736285345167153852487417)
          ·
            refine ⟨12552214008875365389365563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16736285345167153852487417 12552214008875365389365563)
            ·
              refine ⟨18828321013313048084048345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12552214008875365389365563 18828321013313048084048345)
              ·
                refine ⟨14121240759984786063036259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18828321013313048084048345 14121240759984786063036259)
                ·
                  refine ⟨21181861139977179094554389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14121240759984786063036259 21181861139977179094554389)
                  ·
                    refine ⟨992899740936430270057237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21181861139977179094554389 992899740936430270057237)
                    ·
                      rfl

theorem cell23_5800996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 1, 6].length) (baseStart_5800996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5800996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5800996 prefixEnd_5800996 := by exact prefixLift 5800996
  have htrace : WordTrace (prefixWord ++ tailWord_5800996) baseStart_5800996 baseEnd_5800996 := by
    simpa [prefixWord, tailWord_5800996, baseEnd_5800996] using wordTrace_append hprefix tailTrace_5800996
  have hstable : (prefixWord ++ tailWord_5800996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5800996).length < 2 ^ (prefixWord ++ tailWord_5800996).sum := by decide
  have hdescent : baseEnd_5800996 < baseStart_5800996 := by decide
  rcases family_descends (prefixWord ++ tailWord_5800996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5801014 : List Nat := [5, 1, 2, 1, 1, 4, 2, 2, 1, 1, 3]
def baseStart_5801014 : Nat := 118140960795 + 5801014 * 2 ^ 59
def prefixEnd_5801014 : Nat := 4983230072969 + 3 ^ 40 * 5801014 * 2
def baseEnd_5801014 : Nat := 2978708465461071739746629

theorem tailTrace_5801014 : CollatzResearch.WordTrace tailWord_5801014 prefixEnd_5801014 2978708465461071739746629 := by
  unfold tailWord_5801014
  simp only [CollatzResearch.WordTrace]
  refine ⟨13223772662870280447495131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141053575070616324773281397 13223772662870280447495131)
  ·
    refine ⟨19835658994305420671242697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13223772662870280447495131 19835658994305420671242697)
    ·
      refine ⟨14876744245729065503432023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19835658994305420671242697 14876744245729065503432023)
      ·
        refine ⟨22315116368593598255148035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14876744245729065503432023 22315116368593598255148035)
        ·
          refine ⟨33472674552890397382722053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22315116368593598255148035 33472674552890397382722053)
          ·
            refine ⟨6276126478666949509260385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33472674552890397382722053 6276126478666949509260385)
            ·
              refine ⟨4707094859000212131945289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6276126478666949509260385 4707094859000212131945289)
              ·
                refine ⟨3530321144250159098958967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4707094859000212131945289 3530321144250159098958967)
                ·
                  refine ⟨5295481716375238648438451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3530321144250159098958967 5295481716375238648438451)
                  ·
                    refine ⟨7943222574562857972657677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5295481716375238648438451 7943222574562857972657677)
                    ·
                      refine ⟨2978708465461071739746629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7943222574562857972657677 2978708465461071739746629)
                      ·
                        rfl

theorem cell23_5801014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_5801014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5801014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5801014 prefixEnd_5801014 := by exact prefixLift 5801014
  have htrace : WordTrace (prefixWord ++ tailWord_5801014) baseStart_5801014 baseEnd_5801014 := by
    simpa [prefixWord, tailWord_5801014, baseEnd_5801014] using wordTrace_append hprefix tailTrace_5801014
  have hstable : (prefixWord ++ tailWord_5801014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5801014).length < 2 ^ (prefixWord ++ tailWord_5801014).sum := by decide
  have hdescent : baseEnd_5801014 < baseStart_5801014 := by decide
  rcases family_descends (prefixWord ++ tailWord_5801014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5801030 : List Nat := [6, 1, 1, 1, 1, 2, 2, 3, 2, 4]
def baseStart_5801030 : Nat := 118140960795 + 5801030 * 2 ^ 59
def prefixEnd_5801030 : Nat := 4983230072969 + 3 ^ 40 * 5801030 * 2
def baseEnd_5801030 : Nat := 992905560383847892382185

theorem tailTrace_5801030 : CollatzResearch.WordTrace tailWord_5801030 prefixEnd_5801030 992905560383847892382185 := by
  unfold tailWord_5801030
  simp only [CollatzResearch.WordTrace]
  refine ⟨6611904567933328809140767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 141053964115911014595003029 6611904567933328809140767)
  ·
    refine ⟨9917856851899993213711151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6611904567933328809140767 9917856851899993213711151)
    ·
      refine ⟨14876785277849989820566727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9917856851899993213711151 14876785277849989820566727)
      ·
        refine ⟨22315177916774984730850091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14876785277849989820566727 22315177916774984730850091)
        ·
          refine ⟨33472766875162477096275137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22315177916774984730850091 33472766875162477096275137)
          ·
            refine ⟨25104575156371857822206353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33472766875162477096275137 25104575156371857822206353)
            ·
              refine ⟨18828431367278893366654765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25104575156371857822206353 18828431367278893366654765)
              ·
                refine ⟨7060661762729585012495537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18828431367278893366654765 7060661762729585012495537)
                ·
                  refine ⟨5295496322047188759371653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7060661762729585012495537 5295496322047188759371653)
                  ·
                    refine ⟨992905560383847892382185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5295496322047188759371653 992905560383847892382185)
                    ·
                      rfl

theorem cell23_5801030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_5801030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5801030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5801030 prefixEnd_5801030 := by exact prefixLift 5801030
  have htrace : WordTrace (prefixWord ++ tailWord_5801030) baseStart_5801030 baseEnd_5801030 := by
    simpa [prefixWord, tailWord_5801030, baseEnd_5801030] using wordTrace_append hprefix tailTrace_5801030
  have hstable : (prefixWord ++ tailWord_5801030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5801030).length < 2 ^ (prefixWord ++ tailWord_5801030).sum := by decide
  have hdescent : baseEnd_5801030 < baseStart_5801030 := by decide
  rcases family_descends (prefixWord ++ tailWord_5801030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5801036 : List Nat := [2, 2, 1, 3, 1, 1, 1, 2, 6, 1, 3]
def baseStart_5801036 : Nat := 118140960795 + 5801036 * 2 ^ 59
def prefixEnd_5801036 : Nat := 4983230072969 + 3 ^ 40 * 5801036 * 2
def baseEnd_5801036 : Nat := 2978719762035470653671527

theorem tailTrace_5801036 : CollatzResearch.WordTrace tailWord_5801036 prefixEnd_5801036 2978719762035470653671527 := by
  unfold tailWord_5801036
  simp only [CollatzResearch.WordTrace]
  refine ⟨105790582505922392458611481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141054110007896523278148641 105790582505922392458611481)
  ·
    refine ⟨79342936879441794343958611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105790582505922392458611481 79342936879441794343958611)
    ·
      refine ⟨119014405319162691515937917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79342936879441794343958611 119014405319162691515937917)
      ·
        refine ⟨44630401994686009318476719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119014405319162691515937917 44630401994686009318476719)
        ·
          refine ⟨66945602992029013977715079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44630401994686009318476719 66945602992029013977715079)
          ·
            refine ⟨100418404488043520966572619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66945602992029013977715079 100418404488043520966572619)
            ·
              refine ⟨150627606732065281449858929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100418404488043520966572619 150627606732065281449858929)
              ·
                refine ⟨112970705049048961087394197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150627606732065281449858929 112970705049048961087394197)
                ·
                  refine ⟨5295501799174170050971603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 112970705049048961087394197 5295501799174170050971603)
                  ·
                    refine ⟨7943252698761255076457405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5295501799174170050971603 7943252698761255076457405)
                    ·
                      refine ⟨2978719762035470653671527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7943252698761255076457405 2978719762035470653671527)
                      ·
                        rfl

theorem cell23_5801036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_5801036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5801036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5801036 prefixEnd_5801036 := by exact prefixLift 5801036
  have htrace : WordTrace (prefixWord ++ tailWord_5801036) baseStart_5801036 baseEnd_5801036 := by
    simpa [prefixWord, tailWord_5801036, baseEnd_5801036] using wordTrace_append hprefix tailTrace_5801036
  have hstable : (prefixWord ++ tailWord_5801036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5801036).length < 2 ^ (prefixWord ++ tailWord_5801036).sum := by decide
  have hdescent : baseEnd_5801036 < baseStart_5801036 := by decide
  rcases family_descends (prefixWord ++ tailWord_5801036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5801054 : List Nat := [4, 4, 1, 1, 1, 3, 2, 1, 1, 1, 4]
def baseStart_5801054 : Nat := 118140960795 + 5801054 * 2 ^ 59
def prefixEnd_5801054 : Nat := 4983230072969 + 3 ^ 40 * 5801054 * 2
def baseEnd_5801054 : Nat := 2978729004687251583246445

theorem tailTrace_5801054 : CollatzResearch.WordTrace tailWord_5801054 prefixEnd_5801054 2978729004687251583246445 := by
  unfold tailWord_5801054
  simp only [CollatzResearch.WordTrace]
  refine ⟨26447727690722446748922277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141054547683853049327585477 26447727690722446748922277)
  ·
    refine ⟨4958948942010458765422927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26447727690722446748922277 4958948942010458765422927)
    ·
      refine ⟨7438423413015688148134391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4958948942010458765422927 7438423413015688148134391)
      ·
        refine ⟨11157635119523532222201587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7438423413015688148134391 11157635119523532222201587)
        ·
          refine ⟨16736452679285298333302381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11157635119523532222201587 16736452679285298333302381)
          ·
            refine ⟨6276169754731986874988393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16736452679285298333302381 6276169754731986874988393)
            ·
              refine ⟨4707127316048990156241295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6276169754731986874988393 4707127316048990156241295)
              ·
                refine ⟨7060690974073485234361943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4707127316048990156241295 7060690974073485234361943)
                ·
                  refine ⟨10591036461110227851542915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7060690974073485234361943 10591036461110227851542915)
                  ·
                    refine ⟨15886554691665341777314373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10591036461110227851542915 15886554691665341777314373)
                    ·
                      refine ⟨2978729004687251583246445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15886554691665341777314373 2978729004687251583246445)
                      ·
                        rfl

theorem cell23_5801054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_5801054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5801054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5801054 prefixEnd_5801054 := by exact prefixLift 5801054
  have htrace : WordTrace (prefixWord ++ tailWord_5801054) baseStart_5801054 baseEnd_5801054 := by
    simpa [prefixWord, tailWord_5801054, baseEnd_5801054] using wordTrace_append hprefix tailTrace_5801054
  have hstable : (prefixWord ++ tailWord_5801054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5801054).length < 2 ^ (prefixWord ++ tailWord_5801054).sum := by decide
  have hdescent : baseEnd_5801054 < baseStart_5801054 := by decide
  rcases family_descends (prefixWord ++ tailWord_5801054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5801070 : List Nat := [4, 1, 2, 2, 1, 2, 3, 2, 2, 1, 3]
def baseStart_5801070 : Nat := 118140960795 + 5801070 * 2 ^ 59
def prefixEnd_5801070 : Nat := 4983230072969 + 3 ^ 40 * 5801070 * 2
def baseEnd_5801070 : Nat := 2978737220377723520646371

theorem tailTrace_5801070 : CollatzResearch.WordTrace tailWord_5801070 prefixEnd_5801070 2978737220377723520646371 := by
  unfold tailWord_5801070
  simp only [CollatzResearch.WordTrace]
  refine ⟨26447800636715201090495083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141054936729147739149307109 26447800636715201090495083)
  ·
    refine ⟨39671700955072801635742625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26447800636715201090495083 39671700955072801635742625)
    ·
      refine ⟨29753775716304601226806969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39671700955072801635742625 29753775716304601226806969)
      ·
        refine ⟨22315331787228450920105227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29753775716304601226806969 22315331787228450920105227)
        ·
          refine ⟨33472997680842676380157841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22315331787228450920105227 33472997680842676380157841)
          ·
            refine ⟨25104748260632007285118381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33472997680842676380157841 25104748260632007285118381)
            ·
              refine ⟨9414280597737002731919393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25104748260632007285118381 9414280597737002731919393)
              ·
                refine ⟨7060710448302752048939545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9414280597737002731919393 7060710448302752048939545)
                ·
                  refine ⟨5295532836227064036704659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7060710448302752048939545 5295532836227064036704659)
                  ·
                    refine ⟨7943299254340596055056989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5295532836227064036704659 7943299254340596055056989)
                    ·
                      refine ⟨2978737220377723520646371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7943299254340596055056989 2978737220377723520646371)
                      ·
                        rfl

theorem cell23_5801070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_5801070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5801070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5801070 prefixEnd_5801070 := by exact prefixLift 5801070
  have htrace : WordTrace (prefixWord ++ tailWord_5801070) baseStart_5801070 baseEnd_5801070 := by
    simpa [prefixWord, tailWord_5801070, baseEnd_5801070] using wordTrace_append hprefix tailTrace_5801070
  have hstable : (prefixWord ++ tailWord_5801070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5801070).length < 2 ^ (prefixWord ++ tailWord_5801070).sum := by decide
  have hdescent : baseEnd_5801070 < baseStart_5801070 := by decide
  rcases family_descends (prefixWord ++ tailWord_5801070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
