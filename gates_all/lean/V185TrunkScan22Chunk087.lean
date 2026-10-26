import V185TrunkScan22Chunk086

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_781282 : List Nat := [3, 3, 3, 1, 1, 1, 1, 2, 7]
def baseStart_781282 : Nat := 118140960795 + 781282 * 2 ^ 59
def prefixEnd_781282 : Nat := 4983230072969 + 3 ^ 40 * 781282 * 2
def baseEnd_781282 : Nat := 89149598379137214284879

theorem tailTrace_781282 : CollatzResearch.WordTrace tailWord_781282 prefixEnd_781282 89149598379137214284879 := by
  unfold tailWord_781282
  simp only [CollatzResearch.WordTrace]
  refine ⟨7123923888889055296904525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18997130370370814125078733 7123923888889055296904525)
  ·
    refine ⟨2671471458333395736339197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7123923888889055296904525 2671471458333395736339197)
    ·
      refine ⟨1001801796875023401127199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2671471458333395736339197 1001801796875023401127199)
      ·
        refine ⟨1502702695312535101690799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1001801796875023401127199 1502702695312535101690799)
        ·
          refine ⟨2254054042968802652536199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1502702695312535101690799 2254054042968802652536199)
          ·
            refine ⟨3381081064453203978804299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2254054042968802652536199 3381081064453203978804299)
            ·
              refine ⟨5071621596679805968206449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3381081064453203978804299 5071621596679805968206449)
              ·
                refine ⟨3803716197509854476154837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5071621596679805968206449 3803716197509854476154837)
                ·
                  refine ⟨89149598379137214284879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3803716197509854476154837 89149598379137214284879)
                  ·
                    rfl

theorem cell22_781282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_781282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_781282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_781282 prefixEnd_781282 := by exact prefixLift 781282
  have htrace : WordTrace (prefixWord ++ tailWord_781282) baseStart_781282 baseEnd_781282 := by
    simpa [prefixWord, tailWord_781282, baseEnd_781282] using wordTrace_append hprefix tailTrace_781282
  have hstable : (prefixWord ++ tailWord_781282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781282).length < 2 ^ (prefixWord ++ tailWord_781282).sum := by decide
  have hdescent : baseEnd_781282 < baseStart_781282 := by decide
  rcases family_descends (prefixWord ++ tailWord_781282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781372 : List Nat := [2, 2, 2, 2, 2, 4, 1, 7]
def baseStart_781372 : Nat := 118140960795 + 781372 * 2 ^ 59
def prefixEnd_781372 : Nat := 4983230072969 + 3 ^ 40 * 781372 * 2
def baseEnd_781372 : Nat := 29719955997409045344929

theorem tailTrace_781372 : CollatzResearch.WordTrace tailWord_781372 prefixEnd_781372 29719955997409045344929 := by
  unfold tailWord_781372
  simp only [CollatzResearch.WordTrace]
  refine ⟨14249489062615083279197185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18999318750153444372262913 14249489062615083279197185)
  ·
    refine ⟨10687116796961312459397889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14249489062615083279197185 10687116796961312459397889)
    ·
      refine ⟨8015337597720984344548417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10687116796961312459397889 8015337597720984344548417)
      ·
        refine ⟨6011503198290738258411313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8015337597720984344548417 6011503198290738258411313)
        ·
          refine ⟨4508627398718053693808485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6011503198290738258411313 4508627398718053693808485)
          ·
            refine ⟨845367637259635067589091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4508627398718053693808485 845367637259635067589091)
            ·
              refine ⟨1268051455889452601383637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 845367637259635067589091 1268051455889452601383637)
              ·
                refine ⟨29719955997409045344929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1268051455889452601383637 29719955997409045344929)
                ·
                  rfl

theorem cell22_781372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 7].length) (baseStart_781372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_781372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_781372 prefixEnd_781372 := by exact prefixLift 781372
  have htrace : WordTrace (prefixWord ++ tailWord_781372) baseStart_781372 baseEnd_781372 := by
    simpa [prefixWord, tailWord_781372, baseEnd_781372] using wordTrace_append hprefix tailTrace_781372
  have hstable : (prefixWord ++ tailWord_781372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781372).length < 2 ^ (prefixWord ++ tailWord_781372).sum := by decide
  have hdescent : baseEnd_781372 < baseStart_781372 := by decide
  rcases family_descends (prefixWord ++ tailWord_781372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781389 : List Nat := [1, 6, 1, 1, 1, 3, 3, 6]
def baseStart_781389 : Nat := 118140960795 + 781389 * 2 ^ 59
def prefixEnd_781389 : Nat := 4983230072969 + 3 ^ 40 * 781389 * 2
def baseEnd_781389 : Nat := 29720602602677670047701

theorem tailTrace_781389 : CollatzResearch.WordTrace tailWord_781389 prefixEnd_781389 29720602602677670047701 := by
  unfold tailWord_781389
  simp only [CollatzResearch.WordTrace]
  refine ⟨28499598166168578461763221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18999732110779052307842147 28499598166168578461763221)
  ·
    refine ⟨1335918664039152115395151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 28499598166168578461763221 1335918664039152115395151)
    ·
      refine ⟨2003877996058728173092727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1335918664039152115395151 2003877996058728173092727)
      ·
        refine ⟨3005816994088092259639091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2003877996058728173092727 3005816994088092259639091)
        ·
          refine ⟨4508725491132138389458637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3005816994088092259639091 4508725491132138389458637)
          ·
            refine ⟨1690772059174551896046989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4508725491132138389458637 1690772059174551896046989)
            ·
              refine ⟨634039522190456961017621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1690772059174551896046989 634039522190456961017621)
              ·
                refine ⟨29720602602677670047701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 634039522190456961017621 29720602602677670047701)
                ·
                  rfl

theorem cell22_781389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 6].length) (baseStart_781389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_781389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_781389 prefixEnd_781389 := by exact prefixLift 781389
  have htrace : WordTrace (prefixWord ++ tailWord_781389) baseStart_781389 baseEnd_781389 := by
    simpa [prefixWord, tailWord_781389, baseEnd_781389] using wordTrace_append hprefix tailTrace_781389
  have hstable : (prefixWord ++ tailWord_781389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781389).length < 2 ^ (prefixWord ++ tailWord_781389).sum := by decide
  have hdescent : baseEnd_781389 < baseStart_781389 := by decide
  rcases family_descends (prefixWord ++ tailWord_781389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781400 : List Nat := [2, 1, 2, 2, 1, 3, 2, 2, 7]
def baseStart_781400 : Nat := 118140960795 + 781400 * 2 ^ 59
def prefixEnd_781400 : Nat := 4983230072969 + 3 ^ 40 * 781400 * 2
def baseEnd_781400 : Nat := 89163062982966222801425

theorem tailTrace_781400 : CollatzResearch.WordTrace tailWord_781400 prefixEnd_781400 89163062982966222801425 := by
  unfold tailWord_781400
  simp only [CollatzResearch.WordTrace]
  refine ⟨14249999684564363670206827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18999999579419151560275769 14249999684564363670206827)
  ·
    refine ⟨21374999526846545505310241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14249999684564363670206827 21374999526846545505310241)
    ·
      refine ⟨16031249645134909128982681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21374999526846545505310241 16031249645134909128982681)
      ·
        refine ⟨12023437233851181846737011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16031249645134909128982681 12023437233851181846737011)
        ·
          refine ⟨18035155850776772770105517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12023437233851181846737011 18035155850776772770105517)
          ·
            refine ⟨6763183444041289788789569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18035155850776772770105517 6763183444041289788789569)
            ·
              refine ⟨5072387583030967341592177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6763183444041289788789569 5072387583030967341592177)
              ·
                refine ⟨3804290687273225506194133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5072387583030967341592177 3804290687273225506194133)
                ·
                  refine ⟨89163062982966222801425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3804290687273225506194133 89163062982966222801425)
                  ·
                    rfl

theorem cell22_781400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 7].length) (baseStart_781400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_781400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_781400 prefixEnd_781400 := by exact prefixLift 781400
  have htrace : WordTrace (prefixWord ++ tailWord_781400) baseStart_781400 baseEnd_781400 := by
    simpa [prefixWord, tailWord_781400, baseEnd_781400] using wordTrace_append hprefix tailTrace_781400
  have hstable : (prefixWord ++ tailWord_781400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781400).length < 2 ^ (prefixWord ++ tailWord_781400).sum := by decide
  have hdescent : baseEnd_781400 < baseStart_781400 := by decide
  rcases family_descends (prefixWord ++ tailWord_781400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781417 : List Nat := [1, 2, 1, 1, 1, 6, 3, 2, 5]
def baseStart_781417 : Nat := 118140960795 + 781417 * 2 ^ 59
def prefixEnd_781417 : Nat := 4983230072969 + 3 ^ 40 * 781417 * 2
def baseEnd_781417 : Nat := 89165002798772096909741

theorem tailTrace_781417 : CollatzResearch.WordTrace tailWord_781417 prefixEnd_781417 89165002798772096909741 := by
  unfold tailWord_781417
  simp only [CollatzResearch.WordTrace]
  refine ⟨28500619410067139243782505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19000412940044759495855003 28500619410067139243782505)
  ·
    refine ⟨21375464557550354432836879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28500619410067139243782505 21375464557550354432836879)
    ·
      refine ⟨32063196836325531649255319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21375464557550354432836879 32063196836325531649255319)
      ·
        refine ⟨48094795254488297473882979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32063196836325531649255319 48094795254488297473882979)
        ·
          refine ⟨72142192881732446210824469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48094795254488297473882979 72142192881732446210824469)
          ·
            refine ⟨3381665291331208416132397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 72142192881732446210824469 3381665291331208416132397)
            ·
              refine ⟨1268124484249203156049649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3381665291331208416132397 1268124484249203156049649)
              ·
                refine ⟨951093363186902367037237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1268124484249203156049649 951093363186902367037237)
                ·
                  refine ⟨89165002798772096909741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 951093363186902367037237 89165002798772096909741)
                  ·
                    rfl

theorem cell22_781417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 2, 5].length) (baseStart_781417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_781417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_781417 prefixEnd_781417 := by exact prefixLift 781417
  have htrace : WordTrace (prefixWord ++ tailWord_781417) baseStart_781417 baseEnd_781417 := by
    simpa [prefixWord, tailWord_781417, baseEnd_781417] using wordTrace_append hprefix tailTrace_781417
  have hstable : (prefixWord ++ tailWord_781417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781417).length < 2 ^ (prefixWord ++ tailWord_781417).sum := by decide
  have hdescent : baseEnd_781417 < baseStart_781417 := by decide
  rcases family_descends (prefixWord ++ tailWord_781417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781421 : List Nat := [1, 5, 1, 1, 2, 2, 2, 4, 1, 3]
def baseStart_781421 : Nat := 118140960795 + 781421 * 2 ^ 59
def prefixEnd_781421 : Nat := 4983230072969 + 3 ^ 40 * 781421 * 2
def baseEnd_781421 : Nat := 267496377678061613629211

theorem tailTrace_781421 : CollatzResearch.WordTrace tailWord_781421 prefixEnd_781421 267496377678061613629211 := by
  unfold tailWord_781421
  simp only [CollatzResearch.WordTrace]
  refine ⟨28500765302052647926928117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19000510201368431951285411 28500765302052647926928117)
  ·
    refine ⟨2671946747067435743149511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28500765302052647926928117 2671946747067435743149511)
    ·
      refine ⟨4007920120601153614724267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2671946747067435743149511 4007920120601153614724267)
      ·
        refine ⟨6011880180901730422086401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4007920120601153614724267 6011880180901730422086401)
        ·
          refine ⟨4508910135676297816564801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6011880180901730422086401 4508910135676297816564801)
          ·
            refine ⟨3381682601757223362423601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4508910135676297816564801 3381682601757223362423601)
            ·
              refine ⟨2536261951317917521817701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3381682601757223362423601 2536261951317917521817701)
              ·
                refine ⟨475549115872109535340819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2536261951317917521817701 475549115872109535340819)
                ·
                  refine ⟨713323673808164303011229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 475549115872109535340819 713323673808164303011229)
                  ·
                    refine ⟨267496377678061613629211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 713323673808164303011229 267496377678061613629211)
                    ·
                      rfl

theorem cell22_781421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_781421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_781421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_781421 prefixEnd_781421 := by exact prefixLift 781421
  have htrace : WordTrace (prefixWord ++ tailWord_781421) baseStart_781421 baseEnd_781421 := by
    simpa [prefixWord, tailWord_781421, baseEnd_781421] using wordTrace_append hprefix tailTrace_781421
  have hstable : (prefixWord ++ tailWord_781421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781421).length < 2 ^ (prefixWord ++ tailWord_781421).sum := by decide
  have hdescent : baseEnd_781421 < baseStart_781421 := by decide
  rcases family_descends (prefixWord ++ tailWord_781421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781464 : List Nat := [2, 1, 2, 4, 2, 1, 2, 3, 1, 4]
def baseStart_781464 : Nat := 118140960795 + 781464 * 2 ^ 59
def prefixEnd_781464 : Nat := 4983230072969 + 3 ^ 40 * 781464 * 2
def baseEnd_781464 : Nat := 267511097456823834804079

theorem tailTrace_781464 : CollatzResearch.WordTrace tailWord_781464 prefixEnd_781464 267511097456823834804079 := by
  unfold tailWord_781464
  simp only [CollatzResearch.WordTrace]
  refine ⟨14251166820448433135371723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19001555760597910847162297 14251166820448433135371723)
  ·
    refine ⟨21376750230672649703057585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14251166820448433135371723 21376750230672649703057585)
    ·
      refine ⟨16032562673004487277293189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21376750230672649703057585 16032562673004487277293189)
      ·
        refine ⟨3006105501188341364492473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16032562673004487277293189 3006105501188341364492473)
        ·
          refine ⟨2254579125891256023369355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3006105501188341364492473 2254579125891256023369355)
          ·
            refine ⟨3381868688836884035054033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2254579125891256023369355 3381868688836884035054033)
            ·
              refine ⟨2536401516627663026290525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3381868688836884035054033 2536401516627663026290525)
              ·
                refine ⟨951150568735373634858947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2536401516627663026290525 951150568735373634858947)
                ·
                  refine ⟨1426725853103060452288421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 951150568735373634858947 1426725853103060452288421)
                  ·
                    refine ⟨267511097456823834804079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1426725853103060452288421 267511097456823834804079)
                    ·
                      rfl

theorem cell22_781464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 3, 1, 4].length) (baseStart_781464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_781464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_781464 prefixEnd_781464 := by exact prefixLift 781464
  have htrace : WordTrace (prefixWord ++ tailWord_781464) baseStart_781464 baseEnd_781464 := by
    simpa [prefixWord, tailWord_781464, baseEnd_781464] using wordTrace_append hprefix tailTrace_781464
  have hstable : (prefixWord ++ tailWord_781464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781464).length < 2 ^ (prefixWord ++ tailWord_781464).sum := by decide
  have hdescent : baseEnd_781464 < baseStart_781464 := by decide
  rcases family_descends (prefixWord ++ tailWord_781464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781479 : List Nat := [1, 1, 6, 2, 1, 1, 3, 1, 6]
def baseStart_781479 : Nat := 118140960795 + 781479 * 2 ^ 59
def prefixEnd_781479 : Nat := 4983230072969 + 3 ^ 40 * 781479 * 2
def baseEnd_781479 : Nat := 89172077421122931893011

theorem tailTrace_781479 : CollatzResearch.WordTrace tailWord_781479 prefixEnd_781479 89172077421122931893011 := by
  unfold tailWord_781479
  simp only [CollatzResearch.WordTrace]
  refine ⟨28502880735842523832539491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19001920490561682555026327 28502880735842523832539491)
  ·
    refine ⟨42754321103763785748809237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28502880735842523832539491 42754321103763785748809237)
    ·
      refine ⟨2004108801738927456975433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 42754321103763785748809237 2004108801738927456975433)
      ·
        refine ⟨1503081601304195592731575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2004108801738927456975433 1503081601304195592731575)
        ·
          refine ⟨2254622401956293389097363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1503081601304195592731575 2254622401956293389097363)
          ·
            refine ⟨3381933602934440083646045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2254622401956293389097363 3381933602934440083646045)
            ·
              refine ⟨1268225101100415031367267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3381933602934440083646045 1268225101100415031367267)
              ·
                refine ⟨1902337651650622547050901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1268225101100415031367267 1902337651650622547050901)
                ·
                  refine ⟨89172077421122931893011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1902337651650622547050901 89172077421122931893011)
                  ·
                    rfl

theorem cell22_781479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 6].length) (baseStart_781479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_781479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_781479 prefixEnd_781479 := by exact prefixLift 781479
  have htrace : WordTrace (prefixWord ++ tailWord_781479) baseStart_781479 baseEnd_781479 := by
    simpa [prefixWord, tailWord_781479, baseEnd_781479] using wordTrace_append hprefix tailTrace_781479
  have hstable : (prefixWord ++ tailWord_781479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781479).length < 2 ^ (prefixWord ++ tailWord_781479).sum := by decide
  have hdescent : baseEnd_781479 < baseStart_781479 := by decide
  rcases family_descends (prefixWord ++ tailWord_781479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781524 : List Nat := [2, 4, 1, 4, 1, 10]
def baseStart_781524 : Nat := 118140960795 + 781524 * 2 ^ 59
def prefixEnd_781524 : Nat := 4983230072969 + 3 ^ 40 * 781524 * 2
def baseEnd_781524 : Nat := 3302859712135847880295

theorem tailTrace_781524 : CollatzResearch.WordTrace tailWord_781524 prefixEnd_781524 3302859712135847880295 := by
  unfold tailWord_781524
  simp only [CollatzResearch.WordTrace]
  refine ⟨14252261010339748258963813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19003014680452997678618417 14252261010339748258963813)
  ·
    refine ⟨2672298939438702798555715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14252261010339748258963813 2672298939438702798555715)
    ·
      refine ⟨4008448409158054197833573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2672298939438702798555715 4008448409158054197833573)
      ·
        refine ⟨751584076717135162093795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4008448409158054197833573 751584076717135162093795)
        ·
          refine ⟨1127376115075702743140693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 751584076717135162093795 1127376115075702743140693)
          ·
            refine ⟨3302859712135847880295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1127376115075702743140693 3302859712135847880295)
            ·
              rfl

theorem cell22_781524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 10].length) (baseStart_781524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_781524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_781524 prefixEnd_781524 := by exact prefixLift 781524
  have htrace : WordTrace (prefixWord ++ tailWord_781524) baseStart_781524 baseEnd_781524 := by
    simpa [prefixWord, tailWord_781524, baseEnd_781524] using wordTrace_append hprefix tailTrace_781524
  have hstable : (prefixWord ++ tailWord_781524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781524).length < 2 ^ (prefixWord ++ tailWord_781524).sum := by decide
  have hdescent : baseEnd_781524 < baseStart_781524 := by decide
  rcases family_descends (prefixWord ++ tailWord_781524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781537 : List Nat := [1, 2, 3, 1, 3, 2, 1, 1, 2, 6]
def baseStart_781537 : Nat := 118140960795 + 781537 * 2 ^ 59
def prefixEnd_781537 : Nat := 4983230072969 + 3 ^ 40 * 781537 * 2
def baseEnd_781537 : Nat := 267536086848675977728855

theorem tailTrace_781537 : CollatzResearch.WordTrace tailWord_781537 prefixEnd_781537 267536086848675977728855 := by
  unfold tailWord_781537
  simp only [CollatzResearch.WordTrace]
  refine ⟨28504996169632399738150865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19003330779754933158767243 28504996169632399738150865)
  ·
    refine ⟨21378747127224299803613149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28504996169632399738150865 21378747127224299803613149)
    ·
      refine ⟨8017030172709112426354931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21378747127224299803613149 8017030172709112426354931)
      ·
        refine ⟨12025545259063668639532397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8017030172709112426354931 12025545259063668639532397)
        ·
          refine ⟨4509579472148875739824649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12025545259063668639532397 4509579472148875739824649)
          ·
            refine ⟨3382184604111656804868487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4509579472148875739824649 3382184604111656804868487)
            ·
              refine ⟨5073276906167485207302731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3382184604111656804868487 5073276906167485207302731)
              ·
                refine ⟨7609915359251227810954097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5073276906167485207302731 7609915359251227810954097)
                ·
                  refine ⟨5707436519438420858215573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7609915359251227810954097 5707436519438420858215573)
                  ·
                    refine ⟨267536086848675977728855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5707436519438420858215573 267536086848675977728855)
                    ·
                      rfl

theorem cell22_781537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_781537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_781537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_781537 prefixEnd_781537 := by exact prefixLift 781537
  have htrace : WordTrace (prefixWord ++ tailWord_781537) baseStart_781537 baseEnd_781537 := by
    simpa [prefixWord, tailWord_781537, baseEnd_781537] using wordTrace_append hprefix tailTrace_781537
  have hstable : (prefixWord ++ tailWord_781537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781537).length < 2 ^ (prefixWord ++ tailWord_781537).sum := by decide
  have hdescent : baseEnd_781537 < baseStart_781537 := by decide
  rcases family_descends (prefixWord ++ tailWord_781537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781541 : List Nat := [1, 3, 1, 4, 4, 1, 1, 7]
def baseStart_781541 : Nat := 118140960795 + 781541 * 2 ^ 59
def prefixEnd_781541 : Nat := 4983230072969 + 3 ^ 40 * 781541 * 2
def baseEnd_781541 : Nat := 29726384014491255625427

theorem tailTrace_781541 : CollatzResearch.WordTrace tailWord_781541 prefixEnd_781541 29726384014491255625427 := by
  unfold tailWord_781541
  simp only [CollatzResearch.WordTrace]
  refine ⟨28505142061617908421296477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19003428041078605614197651 28505142061617908421296477)
  ·
    refine ⟨10689428273106715657986179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28505142061617908421296477 10689428273106715657986179)
    ·
      refine ⟨16034142409660073486979269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10689428273106715657986179 16034142409660073486979269)
      ·
        refine ⟨3006401701811263778808613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16034142409660073486979269 3006401701811263778808613)
        ·
          refine ⟨563700319089611958526615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3006401701811263778808613 563700319089611958526615)
          ·
            refine ⟨845550478634417937789923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 563700319089611958526615 845550478634417937789923)
            ·
              refine ⟨1268325717951626906684885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 845550478634417937789923 1268325717951626906684885)
              ·
                refine ⟨29726384014491255625427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1268325717951626906684885 29726384014491255625427)
                ·
                  rfl

theorem cell22_781541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 7].length) (baseStart_781541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_781541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_781541 prefixEnd_781541 := by exact prefixLift 781541
  have htrace : WordTrace (prefixWord ++ tailWord_781541) baseStart_781541 baseEnd_781541 := by
    simpa [prefixWord, tailWord_781541, baseEnd_781541] using wordTrace_append hprefix tailTrace_781541
  have hstable : (prefixWord ++ tailWord_781541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781541).length < 2 ^ (prefixWord ++ tailWord_781541).sum := by decide
  have hdescent : baseEnd_781541 < baseStart_781541 := by decide
  rcases family_descends (prefixWord ++ tailWord_781541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781631 : List Nat := [1, 1, 2, 2, 4, 2, 3, 3, 4]
def baseStart_781631 : Nat := 118140960795 + 781631 * 2 ^ 59
def prefixEnd_781631 : Nat := 4983230072969 + 3 ^ 40 * 781631 * 2
def baseEnd_781631 : Nat := 89189421656563688626189

theorem tailTrace_781631 : CollatzResearch.WordTrace tailWord_781631 prefixEnd_781631 89189421656563688626189 := by
  unfold tailWord_781631
  simp only [CollatzResearch.WordTrace]
  refine ⟨28508424631291853792072747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19005616420861235861381831 28508424631291853792072747)
  ·
    refine ⟨42762636946937780688109121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28508424631291853792072747 42762636946937780688109121)
    ·
      refine ⟨32071977710203335516081841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42762636946937780688109121 32071977710203335516081841)
      ·
        refine ⟨24053983282652501637061381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32071977710203335516081841 24053983282652501637061381)
        ·
          refine ⟨4510121865497344056949009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24053983282652501637061381 4510121865497344056949009)
          ·
            refine ⟨3382591399123008042711757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4510121865497344056949009 3382591399123008042711757)
            ·
              refine ⟨1268471774671128016016909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3382591399123008042711757 1268471774671128016016909)
              ·
                refine ⟨475676915501673006006341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1268471774671128016016909 475676915501673006006341)
                ·
                  refine ⟨89189421656563688626189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 475676915501673006006341 89189421656563688626189)
                  ·
                    rfl

theorem cell22_781631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 3, 4].length) (baseStart_781631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_781631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_781631 prefixEnd_781631 := by exact prefixLift 781631
  have htrace : WordTrace (prefixWord ++ tailWord_781631) baseStart_781631 baseEnd_781631 := by
    simpa [prefixWord, tailWord_781631, baseEnd_781631] using wordTrace_append hprefix tailTrace_781631
  have hstable : (prefixWord ++ tailWord_781631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781631).length < 2 ^ (prefixWord ++ tailWord_781631).sum := by decide
  have hdescent : baseEnd_781631 < baseStart_781631 := by decide
  rcases family_descends (prefixWord ++ tailWord_781631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781644 : List Nat := [2, 2, 1, 3, 2, 2, 1, 1, 4, 4]
def baseStart_781644 : Nat := 118140960795 + 781644 * 2 ^ 59
def prefixEnd_781644 : Nat := 4983230072969 + 3 ^ 40 * 781644 * 2
def baseEnd_781644 : Nat := 267572715135363365303527

theorem tailTrace_781644 : CollatzResearch.WordTrace tailWord_781644 prefixEnd_781644 267572715135363365303527 := by
  unfold tailWord_781644
  simp only [CollatzResearch.WordTrace]
  refine ⟨14254449390122378506147993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19005932520163171341530657 14254449390122378506147993)
  ·
    refine ⟨10690837042591783879610995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14254449390122378506147993 10690837042591783879610995)
    ·
      refine ⟨16036255563887675819416493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10690837042591783879610995 16036255563887675819416493)
      ·
        refine ⟨6013595836457878432281185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16036255563887675819416493 6013595836457878432281185)
        ·
          refine ⟨4510196877343408824210889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6013595836457878432281185 4510196877343408824210889)
          ·
            refine ⟨3382647658007556618158167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4510196877343408824210889 3382647658007556618158167)
            ·
              refine ⟨5073971487011334927237251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3382647658007556618158167 5073971487011334927237251)
              ·
                refine ⟨7610957230517002390855877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5073971487011334927237251 7610957230517002390855877)
                ·
                  refine ⟨1427054480721937948285477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7610957230517002390855877 1427054480721937948285477)
                  ·
                    refine ⟨267572715135363365303527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1427054480721937948285477 267572715135363365303527)
                    ·
                      rfl

theorem cell22_781644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 4, 4].length) (baseStart_781644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_781644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_781644 prefixEnd_781644 := by exact prefixLift 781644
  have htrace : WordTrace (prefixWord ++ tailWord_781644) baseStart_781644 baseEnd_781644 := by
    simpa [prefixWord, tailWord_781644, baseEnd_781644] using wordTrace_append hprefix tailTrace_781644
  have hstable : (prefixWord ++ tailWord_781644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781644).length < 2 ^ (prefixWord ++ tailWord_781644).sum := by decide
  have hdescent : baseEnd_781644 < baseStart_781644 := by decide
  rcases family_descends (prefixWord ++ tailWord_781644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781646 : List Nat := [4, 1, 1, 1, 1, 1, 4, 4, 2, 3]
def baseStart_781646 : Nat := 118140960795 + 781646 * 2 ^ 59
def prefixEnd_781646 : Nat := 4983230072969 + 3 ^ 40 * 781646 * 2
def baseEnd_781646 : Nat := 267573399776236026753521

theorem tailTrace_781646 : CollatzResearch.WordTrace tailWord_781646 prefixEnd_781646 267573399776236026753521 := by
  unfold tailWord_781646
  simp only [CollatzResearch.WordTrace]
  refine ⟨3563621465779688919233599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19005981150825007569245861 3563621465779688919233599)
  ·
    refine ⟨5345432198669533378850399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3563621465779688919233599 5345432198669533378850399)
    ·
      refine ⟨8018148298004300068275599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5345432198669533378850399 8018148298004300068275599)
      ·
        refine ⟨12027222447006450102413399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8018148298004300068275599 12027222447006450102413399)
        ·
          refine ⟨18040833670509675153620099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12027222447006450102413399 18040833670509675153620099)
          ·
            refine ⟨27061250505764512730430149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18040833670509675153620099 27061250505764512730430149)
            ·
              refine ⟨5073984469830846136955653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27061250505764512730430149 5073984469830846136955653)
              ·
                refine ⟨951372088093283650679185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5073984469830846136955653 951372088093283650679185)
                ·
                  refine ⟨713529066069962738009389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 951372088093283650679185 713529066069962738009389)
                  ·
                    refine ⟨267573399776236026753521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 713529066069962738009389 267573399776236026753521)
                    ·
                      rfl

theorem cell22_781646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 4, 2, 3].length) (baseStart_781646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_781646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_781646 prefixEnd_781646 := by exact prefixLift 781646
  have htrace : WordTrace (prefixWord ++ tailWord_781646) baseStart_781646 baseEnd_781646 := by
    simpa [prefixWord, tailWord_781646, baseEnd_781646] using wordTrace_append hprefix tailTrace_781646
  have hstable : (prefixWord ++ tailWord_781646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781646).length < 2 ^ (prefixWord ++ tailWord_781646).sum := by decide
  have hdescent : baseEnd_781646 < baseStart_781646 := by decide
  rcases family_descends (prefixWord ++ tailWord_781646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781654 : List Nat := [5, 2, 3, 1, 1, 2, 2, 1, 5]
def baseStart_781654 : Nat := 118140960795 + 781654 * 2 ^ 59
def prefixEnd_781654 : Nat := 4983230072969 + 3 ^ 40 * 781654 * 2
def baseEnd_781654 : Nat := 89192046113242224184499

theorem tailTrace_781654 : CollatzResearch.WordTrace tailWord_781654 prefixEnd_781654 89192046113242224184499 := by
  unfold tailWord_781654
  simp only [CollatzResearch.WordTrace]
  refine ⟨1781828969388033045010001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19006175673472352480106677 1781828969388033045010001)
  ·
    refine ⟨1336371727041024783757501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1781828969388033045010001 1336371727041024783757501)
    ·
      refine ⟨501139397640384293909063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1336371727041024783757501 501139397640384293909063)
      ·
        refine ⟨751709096460576440863595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 501139397640384293909063 751709096460576440863595)
        ·
          refine ⟨1127563644690864661295393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 751709096460576440863595 1127563644690864661295393)
          ·
            refine ⟨845672733518148495971545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1127563644690864661295393 845672733518148495971545)
            ·
              refine ⟨634254550138611371978659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 845672733518148495971545 634254550138611371978659)
              ·
                refine ⟨951381825207917057967989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 634254550138611371978659 951381825207917057967989)
                ·
                  refine ⟨89192046113242224184499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 951381825207917057967989 89192046113242224184499)
                  ·
                    rfl

theorem cell22_781654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_781654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_781654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_781654 prefixEnd_781654 := by exact prefixLift 781654
  have htrace : WordTrace (prefixWord ++ tailWord_781654) baseStart_781654 baseEnd_781654 := by
    simpa [prefixWord, tailWord_781654, baseEnd_781654] using wordTrace_append hprefix tailTrace_781654
  have hstable : (prefixWord ++ tailWord_781654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781654).length < 2 ^ (prefixWord ++ tailWord_781654).sum := by decide
  have hdescent : baseEnd_781654 < baseStart_781654 := by decide
  rcases family_descends (prefixWord ++ tailWord_781654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781708 : List Nat := [2, 2, 1, 2, 1, 3, 3, 4, 1, 3]
def baseStart_781708 : Nat := 118140960795 + 781708 * 2 ^ 59
def prefixEnd_781708 : Nat := 4983230072969 + 3 ^ 40 * 781708 * 2
def baseEnd_781708 : Nat := 267594623643288531703331

theorem tailTrace_781708 : CollatzResearch.WordTrace tailWord_781708 prefixEnd_781708 267594623643288531703331 := by
  unfold tailWord_781708
  simp only [CollatzResearch.WordTrace]
  refine ⟨14255616526006447971312889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19007488701341930628417185 14255616526006447971312889)
  ·
    refine ⟨10691712394504835978484667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14255616526006447971312889 10691712394504835978484667)
    ·
      refine ⟨16037568591757253967727001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10691712394504835978484667 16037568591757253967727001)
      ·
        refine ⟨12028176443817940475795251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16037568591757253967727001 12028176443817940475795251)
        ·
          refine ⟨18042264665726910713692877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12028176443817940475795251 18042264665726910713692877)
          ·
            refine ⟨6765849249647591517634829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18042264665726910713692877 6765849249647591517634829)
            ·
              refine ⟨2537193468617846819113061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6765849249647591517634829 2537193468617846819113061)
              ·
                refine ⟨475723775365846278583699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2537193468617846819113061 475723775365846278583699)
                ·
                  refine ⟨713585663048769417875549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 475723775365846278583699 713585663048769417875549)
                  ·
                    refine ⟨267594623643288531703331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 713585663048769417875549 267594623643288531703331)
                    ·
                      rfl

theorem cell22_781708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 4, 1, 3].length) (baseStart_781708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_781708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_781708 prefixEnd_781708 := by exact prefixLift 781708
  have htrace : WordTrace (prefixWord ++ tailWord_781708) baseStart_781708 baseEnd_781708 := by
    simpa [prefixWord, tailWord_781708, baseEnd_781708] using wordTrace_append hprefix tailTrace_781708
  have hstable : (prefixWord ++ tailWord_781708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781708).length < 2 ^ (prefixWord ++ tailWord_781708).sum := by decide
  have hdescent : baseEnd_781708 < baseStart_781708 := by decide
  rcases family_descends (prefixWord ++ tailWord_781708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781751 : List Nat := [1, 1, 3, 1, 3, 2, 3, 3, 1, 4]
def baseStart_781751 : Nat := 118140960795 + 781751 * 2 ^ 59
def prefixEnd_781751 : Nat := 4983230072969 + 3 ^ 40 * 781751 * 2
def baseEnd_781751 : Nat := 267609343422050752878199

theorem tailTrace_781751 : CollatzResearch.WordTrace tailWord_781751 prefixEnd_781751 267609343422050752878199 := by
  unfold tailWord_781751
  simp only [CollatzResearch.WordTrace]
  refine ⟨28512801390857114286441107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19008534260571409524294071 28512801390857114286441107)
  ·
    refine ⟨42769202086285671429661661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28512801390857114286441107 42769202086285671429661661)
    ·
      refine ⟨16038450782357126786123123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42769202086285671429661661 16038450782357126786123123)
      ·
        refine ⟨24057676173535690179184685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16038450782357126786123123 24057676173535690179184685)
        ·
          refine ⟨9021628565075883817194257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24057676173535690179184685 9021628565075883817194257)
          ·
            refine ⟨6766221423806912862895693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9021628565075883817194257 6766221423806912862895693)
            ·
              refine ⟨2537333033927592323585885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6766221423806912862895693 2537333033927592323585885)
              ·
                refine ⟨951499887722847121344707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2537333033927592323585885 951499887722847121344707)
                ·
                  refine ⟨1427249831584270682017061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 951499887722847121344707 1427249831584270682017061)
                  ·
                    refine ⟨267609343422050752878199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1427249831584270682017061 267609343422050752878199)
                    ·
                      rfl

theorem cell22_781751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 4].length) (baseStart_781751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_781751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_781751 prefixEnd_781751 := by exact prefixLift 781751
  have htrace : WordTrace (prefixWord ++ tailWord_781751) baseStart_781751 baseEnd_781751 := by
    simpa [prefixWord, tailWord_781751, baseEnd_781751] using wordTrace_append hprefix tailTrace_781751
  have hstable : (prefixWord ++ tailWord_781751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781751).length < 2 ^ (prefixWord ++ tailWord_781751).sum := by decide
  have hdescent : baseEnd_781751 < baseStart_781751 := by decide
  rcases family_descends (prefixWord ++ tailWord_781751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781813 : List Nat := [1, 3, 5, 1, 1, 1, 1, 1, 4, 4]
def baseStart_781813 : Nat := 118140960795 + 781813 * 2 ^ 59
def prefixEnd_781813 : Nat := 4983230072969 + 3 ^ 40 * 781813 * 2
def baseEnd_781813 : Nat := 267630567289103257828009

theorem tailTrace_781813 : CollatzResearch.WordTrace tailWord_781813 prefixEnd_781813 267630567289103257828009 := by
  unfold tailWord_781813
  simp only [CollatzResearch.WordTrace]
  refine ⟨28515062716632498875198093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19010041811088332583465395 28515062716632498875198093)
  ·
    refine ⟨10693148518737187078199285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28515062716632498875198093 10693148518737187078199285)
    ·
      refine ⟨1002482673631611288581183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10693148518737187078199285 1002482673631611288581183)
      ·
        refine ⟨1503724010447416932871775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1002482673631611288581183 1503724010447416932871775)
        ·
          refine ⟨2255586015671125399307663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1503724010447416932871775 2255586015671125399307663)
          ·
            refine ⟨3383379023506688098961495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2255586015671125399307663 3383379023506688098961495)
            ·
              refine ⟨5075068535260032148442243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3383379023506688098961495 5075068535260032148442243)
              ·
                refine ⟨7612602802890048222663365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5075068535260032148442243 7612602802890048222663365)
                ·
                  refine ⟨1427363025541884041749381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7612602802890048222663365 1427363025541884041749381)
                  ·
                    refine ⟨267630567289103257828009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1427363025541884041749381 267630567289103257828009)
                    ·
                      rfl

theorem cell22_781813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_781813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_781813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_781813 prefixEnd_781813 := by exact prefixLift 781813
  have htrace : WordTrace (prefixWord ++ tailWord_781813) baseStart_781813 baseEnd_781813 := by
    simpa [prefixWord, tailWord_781813, baseEnd_781813] using wordTrace_append hprefix tailTrace_781813
  have hstable : (prefixWord ++ tailWord_781813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781813).length < 2 ^ (prefixWord ++ tailWord_781813).sum := by decide
  have hdescent : baseEnd_781813 < baseStart_781813 := by decide
  rcases family_descends (prefixWord ++ tailWord_781813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781828 : List Nat := [2, 3, 2, 3, 2, 1, 2, 7]
def baseStart_781828 : Nat := 118140960795 + 781828 * 2 ^ 59
def prefixEnd_781828 : Nat := 4983230072969 + 3 ^ 40 * 781828 * 2
def baseEnd_781828 : Nat := 29737300232849802078107

theorem tailTrace_781828 : CollatzResearch.WordTrace tailWord_781828 prefixEnd_781828 29737300232849802078107 := by
  unfold tailWord_781828
  simp only [CollatzResearch.WordTrace]
  refine ⟨14257804905789078218497069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19010406541052104291329425 14257804905789078218497069)
  ·
    refine ⟨5346676839670904331936401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14257804905789078218497069 5346676839670904331936401)
    ·
      refine ⟨4010007629753178248952301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5346676839670904331936401 4010007629753178248952301)
      ·
        refine ⟨1503752861157441843357113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4010007629753178248952301 1503752861157441843357113)
        ·
          refine ⟨1127814645868081382517835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1503752861157441843357113 1127814645868081382517835)
          ·
            refine ⟨1691721968802122073776753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1127814645868081382517835 1691721968802122073776753)
            ·
              refine ⟨1268791476601591555332565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1691721968802122073776753 1268791476601591555332565)
              ·
                refine ⟨29737300232849802078107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1268791476601591555332565 29737300232849802078107)
                ·
                  rfl

theorem cell22_781828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 7].length) (baseStart_781828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_781828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_781828 prefixEnd_781828 := by exact prefixLift 781828
  have htrace : WordTrace (prefixWord ++ tailWord_781828) baseStart_781828 baseEnd_781828 := by
    simpa [prefixWord, tailWord_781828, baseEnd_781828] using wordTrace_append hprefix tailTrace_781828
  have hstable : (prefixWord ++ tailWord_781828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781828).length < 2 ^ (prefixWord ++ tailWord_781828).sum := by decide
  have hdescent : baseEnd_781828 < baseStart_781828 := by decide
  rcases family_descends (prefixWord ++ tailWord_781828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781877 : List Nat := [1, 3, 3, 1, 1, 3, 4, 2, 1, 3]
def baseStart_781877 : Nat := 118140960795 + 781877 * 2 ^ 59
def prefixEnd_781877 : Nat := 4983230072969 + 3 ^ 40 * 781877 * 2
def baseEnd_781877 : Nat := 267652475797028424227813

theorem tailTrace_781877 : CollatzResearch.WordTrace tailWord_781877 prefixEnd_781877 267652475797028424227813 := by
  unfold tailWord_781877
  simp only [CollatzResearch.WordTrace]
  refine ⟨28517396988400637805527885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19011597992267091870351923 28517396988400637805527885)
  ·
    refine ⟨10694023870650239177072957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28517396988400637805527885 10694023870650239177072957)
    ·
      refine ⟨4010258951493839691402359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10694023870650239177072957 4010258951493839691402359)
      ·
        refine ⟨6015388427240759537103539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4010258951493839691402359 6015388427240759537103539)
        ·
          refine ⟨9023082640861139305655309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6015388427240759537103539 9023082640861139305655309)
          ·
            refine ⟨3383655990322927239620741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9023082640861139305655309 3383655990322927239620741)
            ·
              refine ⟨634435498185548857428889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3383655990322927239620741 634435498185548857428889)
              ·
                refine ⟨475826623639161643071667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 634435498185548857428889 475826623639161643071667)
                ·
                  refine ⟨713739935458742464607501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 475826623639161643071667 713739935458742464607501)
                  ·
                    refine ⟨267652475797028424227813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 713739935458742464607501 267652475797028424227813)
                    ·
                      rfl

theorem cell22_781877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_781877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_781877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_781877 prefixEnd_781877 := by exact prefixLift 781877
  have htrace : WordTrace (prefixWord ++ tailWord_781877) baseStart_781877 baseEnd_781877 := by
    simpa [prefixWord, tailWord_781877, baseEnd_781877] using wordTrace_append hprefix tailTrace_781877
  have hstable : (prefixWord ++ tailWord_781877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781877).length < 2 ^ (prefixWord ++ tailWord_781877).sum := by decide
  have hdescent : baseEnd_781877 < baseStart_781877 := by decide
  rcases family_descends (prefixWord ++ tailWord_781877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781980 : List Nat := [2, 2, 3, 2, 4, 1, 8]
def baseStart_781980 : Nat := 118140960795 + 781980 * 2 ^ 59
def prefixEnd_781980 : Nat := 4983230072969 + 3 ^ 40 * 781980 * 2
def baseEnd_781980 : Nat := 9914360548221129218611

theorem tailTrace_781980 : CollatzResearch.WordTrace tailWord_781980 prefixEnd_781980 9914360548221129218611 := by
  unfold tailWord_781980
  simp only [CollatzResearch.WordTrace]
  refine ⟨14260576853513743198263697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19014102471351657597684929 14260576853513743198263697)
  ·
    refine ⟨10695432640135307398697773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14260576853513743198263697 10695432640135307398697773)
    ·
      refine ⟨4010787240050740274511665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10695432640135307398697773 4010787240050740274511665)
      ·
        refine ⟨3008090430038055205883749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4010787240050740274511665 3008090430038055205883749)
        ·
          refine ⟨564016955632135351103203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3008090430038055205883749 564016955632135351103203)
          ·
            refine ⟨846025433448203026654805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 564016955632135351103203 846025433448203026654805)
            ·
              refine ⟨9914360548221129218611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 846025433448203026654805 9914360548221129218611)
              ·
                rfl

theorem cell22_781980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 8].length) (baseStart_781980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_781980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_781980 prefixEnd_781980 := by exact prefixLift 781980
  have htrace : WordTrace (prefixWord ++ tailWord_781980) baseStart_781980 baseEnd_781980 := by
    simpa [prefixWord, tailWord_781980, baseEnd_781980] using wordTrace_append hprefix tailTrace_781980
  have hstable : (prefixWord ++ tailWord_781980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781980).length < 2 ^ (prefixWord ++ tailWord_781980).sum := by decide
  have hdescent : baseEnd_781980 < baseStart_781980 := by decide
  rcases family_descends (prefixWord ++ tailWord_781980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782021 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 2, 8]
def baseStart_782021 : Nat := 118140960795 + 782021 * 2 ^ 59
def prefixEnd_782021 : Nat := 4983230072969 + 3 ^ 40 * 782021 * 2
def baseEnd_782021 : Nat := 267701769939860048627371

theorem tailTrace_782021 : CollatzResearch.WordTrace tailWord_782021 prefixEnd_782021 267701769939860048627371 := by
  unfold tailWord_782021
  simp only [CollatzResearch.WordTrace]
  refine ⟨28522649099878950398769917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19015099399919300265846611 28522649099878950398769917)
  ·
    refine ⟨10695993412454606399538719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28522649099878950398769917 10695993412454606399538719)
    ·
      refine ⟨16043990118681909599308079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10695993412454606399538719 16043990118681909599308079)
      ·
        refine ⟨24065985178022864398962119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16043990118681909599308079 24065985178022864398962119)
        ·
          refine ⟨36098977767034296598443179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24065985178022864398962119 36098977767034296598443179)
          ·
            refine ⟨54148466650551444897664769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36098977767034296598443179 54148466650551444897664769)
            ·
              refine ⟨40611349987913583673248577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54148466650551444897664769 40611349987913583673248577)
              ·
                refine ⟨30458512490935187754936433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40611349987913583673248577 30458512490935187754936433)
                ·
                  refine ⟨22843884368201390816202325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30458512490935187754936433 22843884368201390816202325)
                  ·
                    refine ⟨267701769939860048627371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 22843884368201390816202325 267701769939860048627371)
                    ·
                      rfl

theorem cell22_782021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 8].length) (baseStart_782021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_782021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_782021 prefixEnd_782021 := by exact prefixLift 782021
  have htrace : WordTrace (prefixWord ++ tailWord_782021) baseStart_782021 baseEnd_782021 := by
    simpa [prefixWord, tailWord_782021, baseEnd_782021] using wordTrace_append hprefix tailTrace_782021
  have hstable : (prefixWord ++ tailWord_782021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782021).length < 2 ^ (prefixWord ++ tailWord_782021).sum := by decide
  have hdescent : baseEnd_782021 < baseStart_782021 := by decide
  rcases family_descends (prefixWord ++ tailWord_782021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782053 : List Nat := [1, 3, 1, 4, 1, 1, 2, 3, 6]
def baseStart_782053 : Nat := 118140960795 + 782053 * 2 ^ 59
def prefixEnd_782053 : Nat := 4983230072969 + 3 ^ 40 * 782053 * 2
def baseEnd_782053 : Nat := 89237574731274210609091

theorem tailTrace_782053 : CollatzResearch.WordTrace tailWord_782053 prefixEnd_782053 89237574731274210609091 := by
  unfold tailWord_782053
  simp only [CollatzResearch.WordTrace]
  refine ⟨28523816235763019863934813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19015877490508679909289875 28523816235763019863934813)
  ·
    refine ⟨10696431088411132448975555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28523816235763019863934813 10696431088411132448975555)
    ·
      refine ⟨16044646632616698673463333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10696431088411132448975555 16044646632616698673463333)
      ·
        refine ⟨3008371243615631001274375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16044646632616698673463333 3008371243615631001274375)
        ·
          refine ⟨4512556865423446501911563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3008371243615631001274375 4512556865423446501911563)
          ·
            refine ⟨6768835298135169752867345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4512556865423446501911563 6768835298135169752867345)
            ·
              refine ⟨5076626473601377314650509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6768835298135169752867345 5076626473601377314650509)
              ·
                refine ⟨1903734927600516492993941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5076626473601377314650509 1903734927600516492993941)
                ·
                  refine ⟨89237574731274210609091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1903734927600516492993941 89237574731274210609091)
                  ·
                    rfl

theorem cell22_782053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 6].length) (baseStart_782053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_782053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_782053 prefixEnd_782053 := by exact prefixLift 782053
  have htrace : WordTrace (prefixWord ++ tailWord_782053) baseStart_782053 baseEnd_782053 := by
    simpa [prefixWord, tailWord_782053, baseEnd_782053] using wordTrace_append hprefix tailTrace_782053
  have hstable : (prefixWord ++ tailWord_782053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782053).length < 2 ^ (prefixWord ++ tailWord_782053).sum := by decide
  have hdescent : baseEnd_782053 < baseStart_782053 := by decide
  rcases family_descends (prefixWord ++ tailWord_782053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782070 : List Nat := [5, 1, 1, 1, 1, 4, 1, 2, 6]
def baseStart_782070 : Nat := 118140960795 + 782070 * 2 ^ 59
def prefixEnd_782070 : Nat := 4983230072969 + 3 ^ 40 * 782070 * 2
def baseEnd_782070 : Nat := 89239514547080084717407

theorem tailTrace_782070 : CollatzResearch.WordTrace tailWord_782070 prefixEnd_782070 89239514547080084717407 := by
  unfold tailWord_782070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1782777267293839485456479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19016290851134287844869109 1782777267293839485456479)
  ·
    refine ⟨2674165900940759228184719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1782777267293839485456479 2674165900940759228184719)
    ·
      refine ⟨4011248851411138842277079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2674165900940759228184719 4011248851411138842277079)
      ·
        refine ⟨6016873277116708263415619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4011248851411138842277079 6016873277116708263415619)
        ·
          refine ⟨9025309915675062395123429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6016873277116708263415619 9025309915675062395123429)
          ·
            refine ⟨1692245609189074199085643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9025309915675062395123429 1692245609189074199085643)
            ·
              refine ⟨2538368413783611298628465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1692245609189074199085643 2538368413783611298628465)
              ·
                refine ⟨1903776310337708473971349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2538368413783611298628465 1903776310337708473971349)
                ·
                  refine ⟨89239514547080084717407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1903776310337708473971349 89239514547080084717407)
                  ·
                    rfl

theorem cell22_782070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_782070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_782070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_782070 prefixEnd_782070 := by exact prefixLift 782070
  have htrace : WordTrace (prefixWord ++ tailWord_782070) baseStart_782070 baseEnd_782070 := by
    simpa [prefixWord, tailWord_782070, baseEnd_782070] using wordTrace_append hprefix tailTrace_782070
  have hstable : (prefixWord ++ tailWord_782070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782070).length < 2 ^ (prefixWord ++ tailWord_782070).sum := by decide
  have hdescent : baseEnd_782070 < baseStart_782070 := by decide
  rcases family_descends (prefixWord ++ tailWord_782070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782093 : List Nat := [1, 7, 2, 1, 1, 2, 1, 2, 5]
def baseStart_782093 : Nat := 118140960795 + 782093 * 2 ^ 59
def prefixEnd_782093 : Nat := 4983230072969 + 3 ^ 40 * 782093 * 2
def baseEnd_782093 : Nat := 89242139003758620275717

theorem tailTrace_782093 : CollatzResearch.WordTrace tailWord_782093 prefixEnd_782093 89242139003758620275717 := by
  unfold tailWord_782093
  simp only [CollatzResearch.WordTrace]
  refine ⟨28525275155618106695390933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19016850103745404463593955 28525275155618106695390933)
  ·
    refine ⟨668561136459799375673225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 28525275155618106695390933 668561136459799375673225)
    ·
      refine ⟨501420852344849531754919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 668561136459799375673225 501420852344849531754919)
      ·
        refine ⟨752131278517274297632379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 501420852344849531754919 752131278517274297632379)
        ·
          refine ⟨1128196917775911446448569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 752131278517274297632379 1128196917775911446448569)
          ·
            refine ⟨846147688331933584836427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1128196917775911446448569 846147688331933584836427)
            ·
              refine ⟨1269221532497900377254641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 846147688331933584836427 1269221532497900377254641)
              ·
                refine ⟨951916149373425282940981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1269221532497900377254641 951916149373425282940981)
                ·
                  refine ⟨89242139003758620275717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 951916149373425282940981 89242139003758620275717)
                  ·
                    rfl

theorem cell22_782093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_782093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_782093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_782093 prefixEnd_782093 := by exact prefixLift 782093
  have htrace : WordTrace (prefixWord ++ tailWord_782093) baseStart_782093 baseEnd_782093 := by
    simpa [prefixWord, tailWord_782093, baseEnd_782093] using wordTrace_append hprefix tailTrace_782093
  have hstable : (prefixWord ++ tailWord_782093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782093).length < 2 ^ (prefixWord ++ tailWord_782093).sum := by decide
  have hdescent : baseEnd_782093 < baseStart_782093 := by decide
  rcases family_descends (prefixWord ++ tailWord_782093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782132 : List Nat := [2, 5, 1, 1, 2, 1, 4, 6]
def baseStart_782132 : Nat := 118140960795 + 782132 * 2 ^ 59
def prefixEnd_782132 : Nat := 4983230072969 + 3 ^ 40 * 782132 * 2
def baseEnd_782132 : Nat := 29748863056476973233559

theorem tailTrace_782132 : CollatzResearch.WordTrace tailWord_782132 prefixEnd_782132 29748863056476973233559 := by
  unfold tailWord_782132
  simp only [CollatzResearch.WordTrace]
  refine ⟨14263348801238408178030325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19017798401651210904040433 14263348801238408178030325)
  ·
    refine ⟨1337188950116100766690343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14263348801238408178030325 1337188950116100766690343)
    ·
      refine ⟨2005783425174151150035515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1337188950116100766690343 2005783425174151150035515)
      ·
        refine ⟨3008675137761226725053273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2005783425174151150035515 3008675137761226725053273)
        ·
          refine ⟨2256506353320920043789955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3008675137761226725053273 2256506353320920043789955)
          ·
            refine ⟨3384759529981380065684933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2256506353320920043789955 3384759529981380065684933)
            ·
              refine ⟨634642411871508762315925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3384759529981380065684933 634642411871508762315925)
              ·
                refine ⟨29748863056476973233559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 634642411871508762315925 29748863056476973233559)
                ·
                  rfl

theorem cell22_782132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 6].length) (baseStart_782132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_782132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_782132 prefixEnd_782132 := by exact prefixLift 782132
  have htrace : WordTrace (prefixWord ++ tailWord_782132) baseStart_782132 baseEnd_782132 := by
    simpa [prefixWord, tailWord_782132, baseEnd_782132] using wordTrace_append hprefix tailTrace_782132
  have hstable : (prefixWord ++ tailWord_782132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782132).length < 2 ^ (prefixWord ++ tailWord_782132).sum := by decide
  have hdescent : baseEnd_782132 < baseStart_782132 := by decide
  rcases family_descends (prefixWord ++ tailWord_782132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782164 : List Nat := [2, 4, 1, 1, 3, 3, 1, 1, 3, 3]
def baseStart_782164 : Nat := 118140960795 + 782164 * 2 ^ 59
def prefixEnd_782164 : Nat := 4983230072969 + 3 ^ 40 * 782164 * 2
def baseEnd_782164 : Nat := 267750721762255342301933

theorem tailTrace_782164 : CollatzResearch.WordTrace tailWord_782164 prefixEnd_782164 267750721762255342301933 := by
  unfold tailWord_782164
  simp only [CollatzResearch.WordTrace]
  refine ⟨14263932369180442910612773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19018576492240590547483697 14263932369180442910612773)
  ·
    refine ⟨2674487319221333045739895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14263932369180442910612773 2674487319221333045739895)
    ·
      refine ⟨4011730978831999568609843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2674487319221333045739895 4011730978831999568609843)
      ·
        refine ⟨6017596468247999352914765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4011730978831999568609843 6017596468247999352914765)
        ·
          refine ⟨2256598675592999757343037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6017596468247999352914765 2256598675592999757343037)
          ·
            refine ⟨846224503347374909003639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2256598675592999757343037 846224503347374909003639)
            ·
              refine ⟨1269336755021062363505459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 846224503347374909003639 1269336755021062363505459)
              ·
                refine ⟨1904005132531593545258189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1269336755021062363505459 1904005132531593545258189)
                ·
                  refine ⟨714001924699347579471821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1904005132531593545258189 714001924699347579471821)
                  ·
                    refine ⟨267750721762255342301933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 714001924699347579471821 267750721762255342301933)
                    ·
                      rfl

theorem cell22_782164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_782164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_782164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_782164 prefixEnd_782164 := by exact prefixLift 782164
  have htrace : WordTrace (prefixWord ++ tailWord_782164) baseStart_782164 baseEnd_782164 := by
    simpa [prefixWord, tailWord_782164, baseEnd_782164] using wordTrace_append hprefix tailTrace_782164
  have hstable : (prefixWord ++ tailWord_782164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782164).length < 2 ^ (prefixWord ++ tailWord_782164).sum := by decide
  have hdescent : baseEnd_782164 < baseStart_782164 := by decide
  rcases family_descends (prefixWord ++ tailWord_782164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782237 : List Nat := [1, 4, 2, 1, 2, 3, 2, 1, 1, 5]
def baseStart_782237 : Nat := 118140960795 + 782237 * 2 ^ 59
def prefixEnd_782237 : Nat := 4983230072969 + 3 ^ 40 * 782237 * 2
def baseEnd_782237 : Nat := 267775711154107485226709

theorem tailTrace_782237 : CollatzResearch.WordTrace tailWord_782237 prefixEnd_782237 267775711154107485226709 := by
  unfold tailWord_782237
  simp only [CollatzResearch.WordTrace]
  refine ⟨28530527267096419288632965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19020351511397612859088643 28530527267096419288632965)
  ·
    refine ⟨5349473862580578616618681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28530527267096419288632965 5349473862580578616618681)
    ·
      refine ⟨4012105396935433962464011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5349473862580578616618681 4012105396935433962464011)
      ·
        refine ⟨6018158095403150943696017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4012105396935433962464011 6018158095403150943696017)
        ·
          refine ⟨4513618571552363207772013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6018158095403150943696017 4513618571552363207772013)
          ·
            refine ⟨1692606964332136202914505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4513618571552363207772013 1692606964332136202914505)
            ·
              refine ⟨1269455223249102152185879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1692606964332136202914505 1269455223249102152185879)
              ·
                refine ⟨1904182834873653228278819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1269455223249102152185879 1904182834873653228278819)
                ·
                  refine ⟨2856274252310479842418229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1904182834873653228278819 2856274252310479842418229)
                  ·
                    refine ⟨267775711154107485226709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2856274252310479842418229 267775711154107485226709)
                    ·
                      rfl

theorem cell22_782237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_782237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_782237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_782237 prefixEnd_782237 := by exact prefixLift 782237
  have htrace : WordTrace (prefixWord ++ tailWord_782237) baseStart_782237 baseEnd_782237 := by
    simpa [prefixWord, tailWord_782237, baseEnd_782237] using wordTrace_append hprefix tailTrace_782237
  have hstable : (prefixWord ++ tailWord_782237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782237).length < 2 ^ (prefixWord ++ tailWord_782237).sum := by decide
  have hdescent : baseEnd_782237 < baseStart_782237 := by decide
  rcases family_descends (prefixWord ++ tailWord_782237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782282 : List Nat := [3, 1, 2, 1, 2, 1, 3, 3, 3, 3]
def baseStart_782282 : Nat := 118140960795 + 782282 * 2 ^ 59
def prefixEnd_782282 : Nat := 4983230072969 + 3 ^ 40 * 782282 * 2
def baseEnd_782282 : Nat := 267791115573742367851571

theorem tailTrace_782282 : CollatzResearch.WordTrace tailWord_782282 prefixEnd_782282 267791115573742367851571 := by
  unfold tailWord_782282
  simp only [CollatzResearch.WordTrace]
  refine ⟨7133042137983347993505275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19021445701288927982680733 7133042137983347993505275)
  ·
    refine ⟨10699563206975021990257913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7133042137983347993505275 10699563206975021990257913)
    ·
      refine ⟨8024672405231266492693435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10699563206975021990257913 8024672405231266492693435)
      ·
        refine ⟨12037008607846899739040153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8024672405231266492693435 12037008607846899739040153)
        ·
          refine ⟨9027756455885174804280115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12037008607846899739040153 9027756455885174804280115)
          ·
            refine ⟨13541634683827762206420173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9027756455885174804280115 13541634683827762206420173)
            ·
              refine ⟨5078113006435410827407565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13541634683827762206420173 5078113006435410827407565)
              ·
                refine ⟨1904292377413279060277837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5078113006435410827407565 1904292377413279060277837)
                ·
                  refine ⟨714109641529979647604189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1904292377413279060277837 714109641529979647604189)
                  ·
                    refine ⟨267791115573742367851571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 714109641529979647604189 267791115573742367851571)
                    ·
                      rfl

theorem cell22_782282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 3, 3].length) (baseStart_782282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_782282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_782282 prefixEnd_782282 := by exact prefixLift 782282
  have htrace : WordTrace (prefixWord ++ tailWord_782282) baseStart_782282 baseEnd_782282 := by
    simpa [prefixWord, tailWord_782282, baseEnd_782282] using wordTrace_append hprefix tailTrace_782282
  have hstable : (prefixWord ++ tailWord_782282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782282).length < 2 ^ (prefixWord ++ tailWord_782282).sum := by decide
  have hdescent : baseEnd_782282 < baseStart_782282 := by decide
  rcases family_descends (prefixWord ++ tailWord_782282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782301 : List Nat := [1, 4, 3, 1, 4, 1, 2, 6]
def baseStart_782301 : Nat := 118140960795 + 782301 * 2 ^ 59
def prefixEnd_782301 : Nat := 4983230072969 + 3 ^ 40 * 782301 * 2
def baseEnd_782301 : Nat := 29755291073559183514057

theorem tailTrace_782301 : CollatzResearch.WordTrace tailWord_782301 prefixEnd_782301 29755291073559183514057 := by
  unfold tailWord_782301
  simp only [CollatzResearch.WordTrace]
  refine ⟨28532861538864558218962757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19021907692576372145975171 28532861538864558218962757)
  ·
    refine ⟨5349911538537104666055517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28532861538864558218962757 5349911538537104666055517)
    ·
      refine ⟨2006216826951414249770819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5349911538537104666055517 2006216826951414249770819)
      ·
        refine ⟨3009325240427121374656229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2006216826951414249770819 3009325240427121374656229)
        ·
          refine ⟨564248482580085257748043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3009325240427121374656229 564248482580085257748043)
          ·
            refine ⟨846372723870127886622065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 564248482580085257748043 846372723870127886622065)
            ·
              refine ⟨634779542902595914966549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 846372723870127886622065 634779542902595914966549)
              ·
                refine ⟨29755291073559183514057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 634779542902595914966549 29755291073559183514057)
                ·
                  rfl

theorem cell22_782301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 6].length) (baseStart_782301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_782301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_782301 prefixEnd_782301 := by exact prefixLift 782301
  have htrace : WordTrace (prefixWord ++ tailWord_782301) baseStart_782301 baseEnd_782301 := by
    simpa [prefixWord, tailWord_782301, baseEnd_782301] using wordTrace_append hprefix tailTrace_782301
  have hstable : (prefixWord ++ tailWord_782301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782301).length < 2 ^ (prefixWord ++ tailWord_782301).sum := by decide
  have hdescent : baseEnd_782301 < baseStart_782301 := by decide
  rcases family_descends (prefixWord ++ tailWord_782301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782346 : List Nat := [3, 1, 2, 2, 4, 2, 2, 1, 5]
def baseStart_782346 : Nat := 118140960795 + 782346 * 2 ^ 59
def prefixEnd_782346 : Nat := 4983230072969 + 3 ^ 40 * 782346 * 2
def baseEnd_782346 : Nat := 89271008027222511417125

theorem tailTrace_782346 : CollatzResearch.WordTrace tailWord_782346 prefixEnd_782346 89271008027222511417125 := by
  unfold tailWord_782346
  simp only [CollatzResearch.WordTrace]
  refine ⟨7133625705925382726087723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19023001882467687269567261 7133625705925382726087723)
  ·
    refine ⟨10700438558888074089131585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7133625705925382726087723 10700438558888074089131585)
    ·
      refine ⟨8025328919166055566848689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10700438558888074089131585 8025328919166055566848689)
      ·
        refine ⟨6018996689374541675136517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8025328919166055566848689 6018996689374541675136517)
        ·
          refine ⟨1128561879257726564088097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6018996689374541675136517 1128561879257726564088097)
          ·
            refine ⟨846421409443294923066073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1128561879257726564088097 846421409443294923066073)
            ·
              refine ⟨634816057082471192299555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 846421409443294923066073 634816057082471192299555)
              ·
                refine ⟨952224085623706788449333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 634816057082471192299555 952224085623706788449333)
                ·
                  refine ⟨89271008027222511417125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 952224085623706788449333 89271008027222511417125)
                  ·
                    rfl

theorem cell22_782346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 1, 5].length) (baseStart_782346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_782346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_782346 prefixEnd_782346 := by exact prefixLift 782346
  have htrace : WordTrace (prefixWord ++ tailWord_782346) baseStart_782346 baseEnd_782346 := by
    simpa [prefixWord, tailWord_782346, baseEnd_782346] using wordTrace_append hprefix tailTrace_782346
  have hstable : (prefixWord ++ tailWord_782346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782346).length < 2 ^ (prefixWord ++ tailWord_782346).sum := by decide
  have hdescent : baseEnd_782346 < baseStart_782346 := by decide
  rcases family_descends (prefixWord ++ tailWord_782346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782359 : List Nat := [1, 1, 3, 5, 2, 1, 1, 1, 3, 4]
def baseStart_782359 : Nat := 118140960795 + 782359 * 2 ^ 59
def prefixEnd_782359 : Nat := 4983230072969 + 3 ^ 40 * 782359 * 2
def baseEnd_782359 : Nat := 267817474247339833676335

theorem tailTrace_782359 : CollatzResearch.WordTrace tailWord_782359 prefixEnd_782359 267817474247339833676335 := by
  unfold tailWord_782359
  simp only [CollatzResearch.WordTrace]
  refine ⟨28534976972654434124574131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19023317981769622749716087 28534976972654434124574131)
  ·
    refine ⟨42802465458981651186861197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28534976972654434124574131 42802465458981651186861197)
    ·
      refine ⟨16050924547118119195072949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42802465458981651186861197 16050924547118119195072949)
      ·
        refine ⟨1504774176292323674538089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16050924547118119195072949 1504774176292323674538089)
        ·
          refine ⟨1128580632219242755903567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1504774176292323674538089 1128580632219242755903567)
          ·
            refine ⟨1692870948328864133855351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1128580632219242755903567 1692870948328864133855351)
            ·
              refine ⟨2539306422493296200783027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1692870948328864133855351 2539306422493296200783027)
              ·
                refine ⟨3808959633739944301174541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2539306422493296200783027 3808959633739944301174541)
                ·
                  refine ⟨1428359862652479112940453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3808959633739944301174541 1428359862652479112940453)
                  ·
                    refine ⟨267817474247339833676335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1428359862652479112940453 267817474247339833676335)
                    ·
                      rfl

theorem cell22_782359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 3, 4].length) (baseStart_782359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_782359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_782359 prefixEnd_782359 := by exact prefixLift 782359
  have htrace : WordTrace (prefixWord ++ tailWord_782359) baseStart_782359 baseEnd_782359 := by
    simpa [prefixWord, tailWord_782359, baseEnd_782359] using wordTrace_append hprefix tailTrace_782359
  have hstable : (prefixWord ++ tailWord_782359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782359).length < 2 ^ (prefixWord ++ tailWord_782359).sum := by decide
  have hdescent : baseEnd_782359 < baseStart_782359 := by decide
  rcases family_descends (prefixWord ++ tailWord_782359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782385 : List Nat := [1, 2, 2, 3, 1, 13]
def baseStart_782385 : Nat := 118140960795 + 782385 * 2 ^ 59
def prefixEnd_782385 : Nat := 4983230072969 + 3 ^ 40 * 782385 * 2
def baseEnd_782385 : Nat := 3306498451588696697855

theorem tailTrace_782385 : CollatzResearch.WordTrace tailWord_782385 prefixEnd_782385 3306498451588696697855 := by
  unfold tailWord_782385
  simp only [CollatzResearch.WordTrace]
  refine ⟨28535925270560240565020609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19023950180373493710013739 28535925270560240565020609)
  ·
    refine ⟨21401943952920180423765457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28535925270560240565020609 21401943952920180423765457)
    ·
      refine ⟨16051457964690135317824093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21401943952920180423765457 16051457964690135317824093)
      ·
        refine ⟨6019296736758800744184035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16051457964690135317824093 6019296736758800744184035)
        ·
          refine ⟨9028945105138201116276053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6019296736758800744184035 9028945105138201116276053)
          ·
            refine ⟨3306498451588696697855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 9028945105138201116276053 3306498451588696697855)
            ·
              rfl

theorem cell22_782385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 13].length) (baseStart_782385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_782385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_782385 prefixEnd_782385 := by exact prefixLift 782385
  have htrace : WordTrace (prefixWord ++ tailWord_782385) baseStart_782385 baseEnd_782385 := by
    simpa [prefixWord, tailWord_782385, baseEnd_782385] using wordTrace_append hprefix tailTrace_782385
  have hstable : (prefixWord ++ tailWord_782385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782385).length < 2 ^ (prefixWord ++ tailWord_782385).sum := by decide
  have hdescent : baseEnd_782385 < baseStart_782385 := by decide
  rcases family_descends (prefixWord ++ tailWord_782385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782387 : List Nat := [1, 1, 1, 2, 4, 1, 4, 2, 2, 4]
def baseStart_782387 : Nat := 118140960795 + 782387 * 2 ^ 59
def prefixEnd_782387 : Nat := 4983230072969 + 3 ^ 40 * 782387 * 2
def baseEnd_782387 : Nat := 267827059219557093976249

theorem tailTrace_782387 : CollatzResearch.WordTrace tailWord_782387 prefixEnd_782387 267827059219557093976249 := by
  unfold tailWord_782387
  simp only [CollatzResearch.WordTrace]
  refine ⟨28535998216552994906593415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19023998811035329937728943 28535998216552994906593415)
  ·
    refine ⟨42803997324829492359890123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28535998216552994906593415 42803997324829492359890123)
    ·
      refine ⟨64205995987244238539835185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42803997324829492359890123 64205995987244238539835185)
      ·
        refine ⟨48154496990433178904876389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64205995987244238539835185 48154496990433178904876389)
        ·
          refine ⟨9028968185706221044664323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48154496990433178904876389 9028968185706221044664323)
          ·
            refine ⟨13543452278559331566996485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9028968185706221044664323 13543452278559331566996485)
            ·
              refine ⟨2539397302229874668811841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13543452278559331566996485 2539397302229874668811841)
              ·
                refine ⟨1904547976672406001608881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2539397302229874668811841 1904547976672406001608881)
                ·
                  refine ⟨1428410982504304501206661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1904547976672406001608881 1428410982504304501206661)
                  ·
                    refine ⟨267827059219557093976249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1428410982504304501206661 267827059219557093976249)
                    ·
                      rfl

theorem cell22_782387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 2, 4].length) (baseStart_782387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_782387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_782387 prefixEnd_782387 := by exact prefixLift 782387
  have htrace : WordTrace (prefixWord ++ tailWord_782387) baseStart_782387 baseEnd_782387 := by
    simpa [prefixWord, tailWord_782387, baseEnd_782387] using wordTrace_append hprefix tailTrace_782387
  have hstable : (prefixWord ++ tailWord_782387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782387).length < 2 ^ (prefixWord ++ tailWord_782387).sum := by decide
  have hdescent : baseEnd_782387 < baseStart_782387 := by decide
  rcases family_descends (prefixWord ++ tailWord_782387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782389 : List Nat := [1, 3, 3, 1, 1, 1, 3, 4, 2, 3]
def baseStart_782389 : Nat := 118140960795 + 782389 * 2 ^ 59
def prefixEnd_782389 : Nat := 4983230072969 + 3 ^ 40 * 782389 * 2
def baseEnd_782389 : Nat := 267827743860429755426243

theorem tailTrace_782389 : CollatzResearch.WordTrace tailWord_782389 prefixEnd_782389 267827743860429755426243 := by
  unfold tailWord_782389
  simp only [CollatzResearch.WordTrace]
  refine ⟨28536071162545749248166221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19024047441697166165444147 28536071162545749248166221)
  ·
    refine ⟨10701026685954655968062333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28536071162545749248166221 10701026685954655968062333)
    ·
      refine ⟨4012885007232995988023375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10701026685954655968062333 4012885007232995988023375)
      ·
        refine ⟨6019327510849493982035063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4012885007232995988023375 6019327510849493982035063)
        ·
          refine ⟨9028991266274240973052595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6019327510849493982035063 9028991266274240973052595)
          ·
            refine ⟨13543486899411361459578893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9028991266274240973052595 13543486899411361459578893)
            ·
              refine ⟨5078807587279260547342085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13543486899411361459578893 5078807587279260547342085)
              ·
                refine ⟨952276422614861352626641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5078807587279260547342085 952276422614861352626641)
                ·
                  refine ⟨714207316961146014469981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 952276422614861352626641 714207316961146014469981)
                  ·
                    refine ⟨267827743860429755426243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 714207316961146014469981 267827743860429755426243)
                    ·
                      rfl

theorem cell22_782389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_782389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_782389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_782389 prefixEnd_782389 := by exact prefixLift 782389
  have htrace : WordTrace (prefixWord ++ tailWord_782389) baseStart_782389 baseEnd_782389 := by
    simpa [prefixWord, tailWord_782389, baseEnd_782389] using wordTrace_append hprefix tailTrace_782389
  have hstable : (prefixWord ++ tailWord_782389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782389).length < 2 ^ (prefixWord ++ tailWord_782389).sum := by decide
  have hdescent : baseEnd_782389 < baseStart_782389 := by decide
  rcases family_descends (prefixWord ++ tailWord_782389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782406 : List Nat := [6, 1, 1, 1, 1, 1, 4, 1, 1, 5]
def baseStart_782406 : Nat := 118140960795 + 782406 * 2 ^ 59
def prefixEnd_782406 : Nat := 4983230072969 + 3 ^ 40 * 782406 * 2
def baseEnd_782406 : Nat := 267833563307847377751191

theorem tailTrace_782406 : CollatzResearch.WordTrace tailWord_782406 prefixEnd_782406 267833563307847377751191 := by
  unfold tailWord_782406
  simp only [CollatzResearch.WordTrace]
  refine ⟨891771600108880035985471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19024460802322774101023381 891771600108880035985471)
  ·
    refine ⟨1337657400163320053978207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 891771600108880035985471 1337657400163320053978207)
    ·
      refine ⟨2006486100244980080967311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1337657400163320053978207 2006486100244980080967311)
      ·
        refine ⟨3009729150367470121450967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2006486100244980080967311 3009729150367470121450967)
        ·
          refine ⟨4514593725551205182176451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3009729150367470121450967 4514593725551205182176451)
          ·
            refine ⟨6771890588326807773264677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4514593725551205182176451 6771890588326807773264677)
            ·
              refine ⟨1269729485311276457487127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6771890588326807773264677 1269729485311276457487127)
              ·
                refine ⟨1904594227966914686230691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1269729485311276457487127 1904594227966914686230691)
                ·
                  refine ⟨2856891341950372029346037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1904594227966914686230691 2856891341950372029346037)
                  ·
                    refine ⟨267833563307847377751191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2856891341950372029346037 267833563307847377751191)
                    ·
                      rfl

theorem cell22_782406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_782406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_782406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_782406 prefixEnd_782406 := by exact prefixLift 782406
  have htrace : WordTrace (prefixWord ++ tailWord_782406) baseStart_782406 baseEnd_782406 := by
    simpa [prefixWord, tailWord_782406, baseEnd_782406] using wordTrace_append hprefix tailTrace_782406
  have hstable : (prefixWord ++ tailWord_782406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782406).length < 2 ^ (prefixWord ++ tailWord_782406).sum := by decide
  have hdescent : baseEnd_782406 < baseStart_782406 := by decide
  rcases family_descends (prefixWord ++ tailWord_782406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782447 : List Nat := [1, 1, 2, 1, 3, 5, 1, 1, 7]
def baseStart_782447 : Nat := 118140960795 + 782447 * 2 ^ 59
def prefixEnd_782447 : Nat := 4983230072969 + 3 ^ 40 * 782447 * 2
def baseEnd_782447 : Nat := 89282532815245645825355

theorem tailTrace_782447 : CollatzResearch.WordTrace tailWord_782447 prefixEnd_782447 89282532815245645825355 := by
  unfold tailWord_782447
  simp only [CollatzResearch.WordTrace]
  refine ⟨28538186596335625153777595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19025457730890416769185063 28538186596335625153777595)
  ·
    refine ⟨42807279894503437730666393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28538186596335625153777595 42807279894503437730666393)
    ·
      refine ⟨32105459920877578297999795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42807279894503437730666393 32105459920877578297999795)
      ·
        refine ⟨48158189881316367446999693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32105459920877578297999795 48158189881316367446999693)
        ·
          refine ⟨18059321205493637792624885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48158189881316367446999693 18059321205493637792624885)
          ·
            refine ⟨1693061363015028543058583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18059321205493637792624885 1693061363015028543058583)
            ·
              refine ⟨2539592044522542814587875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1693061363015028543058583 2539592044522542814587875)
              ·
                refine ⟨3809388066783814221881813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2539592044522542814587875 3809388066783814221881813)
                ·
                  refine ⟨89282532815245645825355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3809388066783814221881813 89282532815245645825355)
                  ·
                    rfl

theorem cell22_782447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 7].length) (baseStart_782447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_782447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_782447 prefixEnd_782447 := by exact prefixLift 782447
  have htrace : WordTrace (prefixWord ++ tailWord_782447) baseStart_782447 baseEnd_782447 := by
    simpa [prefixWord, tailWord_782447, baseEnd_782447] using wordTrace_append hprefix tailTrace_782447
  have hstable : (prefixWord ++ tailWord_782447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782447).length < 2 ^ (prefixWord ++ tailWord_782447).sum := by decide
  have hdescent : baseEnd_782447 < baseStart_782447 := by decide
  rcases family_descends (prefixWord ++ tailWord_782447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782522 : List Nat := [3, 1, 1, 1, 2, 2, 2, 1, 3, 6]
def baseStart_782522 : Nat := 118140960795 + 782522 * 2 ^ 59
def prefixEnd_782522 : Nat := 4983230072969 + 3 ^ 40 * 782522 * 2
def baseEnd_782522 : Nat := 267873272478461741850835

theorem tailTrace_782522 : CollatzResearch.WordTrace tailWord_782522 prefixEnd_782522 267873272478461741850835 := by
  unfold tailWord_782522
  simp only [CollatzResearch.WordTrace]
  refine ⟨7135230517765978240689455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19027281380709275308505213 7135230517765978240689455)
  ·
    refine ⟨10702845776648967361034183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7135230517765978240689455 10702845776648967361034183)
    ·
      refine ⟨16054268664973451041551275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10702845776648967361034183 16054268664973451041551275)
      ·
        refine ⟨24081402997460176562326913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16054268664973451041551275 24081402997460176562326913)
        ·
          refine ⟨18061052248095132421745185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24081402997460176562326913 18061052248095132421745185)
          ·
            refine ⟨13545789186071349316308889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18061052248095132421745185 13545789186071349316308889)
            ·
              refine ⟨10159341889553511987231667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13545789186071349316308889 10159341889553511987231667)
              ·
                refine ⟨15239012834330267980847501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10159341889553511987231667 15239012834330267980847501)
                ·
                  refine ⟨5714629812873850492817813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15239012834330267980847501 5714629812873850492817813)
                  ·
                    refine ⟨267873272478461741850835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5714629812873850492817813 267873272478461741850835)
                    ·
                      rfl

theorem cell22_782522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 3, 6].length) (baseStart_782522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_782522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_782522 prefixEnd_782522 := by exact prefixLift 782522
  have htrace : WordTrace (prefixWord ++ tailWord_782522) baseStart_782522 baseEnd_782522 := by
    simpa [prefixWord, tailWord_782522, baseEnd_782522] using wordTrace_append hprefix tailTrace_782522
  have hstable : (prefixWord ++ tailWord_782522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782522).length < 2 ^ (prefixWord ++ tailWord_782522).sum := by decide
  have hdescent : baseEnd_782522 < baseStart_782522 := by decide
  rcases family_descends (prefixWord ++ tailWord_782522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782539 : List Nat := [1, 1, 1, 1, 3, 2, 6, 1, 2, 4]
def baseStart_782539 : Nat := 118140960795 + 782539 * 2 ^ 59
def prefixEnd_782539 : Nat := 4983230072969 + 3 ^ 40 * 782539 * 2
def baseEnd_782539 : Nat := 267879091925879364175783

theorem tailTrace_782539 : CollatzResearch.WordTrace tailWord_782539 prefixEnd_782539 267879091925879364175783 := by
  unfold tailWord_782539
  simp only [CollatzResearch.WordTrace]
  refine ⟨28541542112002324866126671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19027694741334883244084447 28541542112002324866126671)
  ·
    refine ⟨42812313168003487299190007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28541542112002324866126671 42812313168003487299190007)
    ·
      refine ⟨64218469752005230948785011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42812313168003487299190007 64218469752005230948785011)
      ·
        refine ⟨96327704628007846423177517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64218469752005230948785011 96327704628007846423177517)
        ·
          refine ⟨36122889235502942408691569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96327704628007846423177517 36122889235502942408691569)
          ·
            refine ⟨27092166926627206806518677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36122889235502942408691569 27092166926627206806518677)
            ·
              refine ⟨1269945324685650319055563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27092166926627206806518677 1269945324685650319055563)
              ·
                refine ⟨1904917987028475478583345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1269945324685650319055563 1904917987028475478583345)
                ·
                  refine ⟨1428688490271356608937509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1904917987028475478583345 1428688490271356608937509)
                  ·
                    refine ⟨267879091925879364175783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1428688490271356608937509 267879091925879364175783)
                    ·
                      rfl

theorem cell22_782539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 2, 4].length) (baseStart_782539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_782539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_782539 prefixEnd_782539 := by exact prefixLift 782539
  have htrace : WordTrace (prefixWord ++ tailWord_782539) baseStart_782539 baseEnd_782539 := by
    simpa [prefixWord, tailWord_782539, baseEnd_782539] using wordTrace_append hprefix tailTrace_782539
  have hstable : (prefixWord ++ tailWord_782539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782539).length < 2 ^ (prefixWord ++ tailWord_782539).sum := by decide
  have hdescent : baseEnd_782539 < baseStart_782539 := by decide
  rcases family_descends (prefixWord ++ tailWord_782539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782586 : List Nat := [3, 1, 1, 1, 1, 6, 1, 2, 3, 3]
def baseStart_782586 : Nat := 118140960795 + 782586 * 2 ^ 59
def prefixEnd_782586 : Nat := 4983230072969 + 3 ^ 40 * 782586 * 2
def baseEnd_782586 : Nat := 267895180986386908250639

theorem tailTrace_782586 : CollatzResearch.WordTrace tailWord_782586 prefixEnd_782586 267895180986386908250639 := by
  unfold tailWord_782586
  simp only [CollatzResearch.WordTrace]
  refine ⟨7135814085708012973271903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19028837561888034595391741 7135814085708012973271903)
  ·
    refine ⟨10703721128562019459907855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7135814085708012973271903 10703721128562019459907855)
    ·
      refine ⟨16055581692843029189861783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10703721128562019459907855 16055581692843029189861783)
      ·
        refine ⟨24083372539264543784792675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16055581692843029189861783 24083372539264543784792675)
        ·
          refine ⟨36125058808896815677189013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24083372539264543784792675 36125058808896815677189013)
          ·
            refine ⟨1693362131667038234868235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 36125058808896815677189013 1693362131667038234868235)
            ·
              refine ⟨2540043197500557352302353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1693362131667038234868235 2540043197500557352302353)
              ·
                refine ⟨1905032398125418014226765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2540043197500557352302353 1905032398125418014226765)
                ·
                  refine ⟨714387149297031755335037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1905032398125418014226765 714387149297031755335037)
                  ·
                    refine ⟨267895180986386908250639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 714387149297031755335037 267895180986386908250639)
                    ·
                      rfl

theorem cell22_782586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 3, 3].length) (baseStart_782586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_782586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_782586 prefixEnd_782586 := by exact prefixLift 782586
  have htrace : WordTrace (prefixWord ++ tailWord_782586) baseStart_782586 baseEnd_782586 := by
    simpa [prefixWord, tailWord_782586, baseEnd_782586] using wordTrace_append hprefix tailTrace_782586
  have hstable : (prefixWord ++ tailWord_782586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782586).length < 2 ^ (prefixWord ++ tailWord_782586).sum := by decide
  have hdescent : baseEnd_782586 < baseStart_782586 := by decide
  rcases family_descends (prefixWord ++ tailWord_782586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782603 : List Nat := [1, 1, 1, 1, 5, 2, 4, 3, 1, 3]
def baseStart_782603 : Nat := 118140960795 + 782603 * 2 ^ 59
def prefixEnd_782603 : Nat := 4983230072969 + 3 ^ 40 * 782603 * 2
def baseEnd_782603 : Nat := 267901000433804530575587

theorem tailTrace_782603 : CollatzResearch.WordTrace tailWord_782603 prefixEnd_782603 267901000433804530575587 := by
  unfold tailWord_782603
  simp only [CollatzResearch.WordTrace]
  refine ⟨28543876383770463796456463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19029250922513642530970975 28543876383770463796456463)
  ·
    refine ⟨42815814575655695694684695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28543876383770463796456463 42815814575655695694684695)
    ·
      refine ⟨64223721863483543542027043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42815814575655695694684695 64223721863483543542027043)
      ·
        refine ⟨96335582795225315313040565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64223721863483543542027043 96335582795225315313040565)
        ·
          refine ⟨9031460887052373310597553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96335582795225315313040565 9031460887052373310597553)
          ·
            refine ⟨6773595665289279982948165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9031460887052373310597553 6773595665289279982948165)
            ·
              refine ⟨1270049187241739996802781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6773595665289279982948165 1270049187241739996802781)
              ·
                refine ⟨476268445215652498801043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1270049187241739996802781 476268445215652498801043)
                ·
                  refine ⟨714402667823478748201565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 476268445215652498801043 714402667823478748201565)
                  ·
                    refine ⟨267901000433804530575587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 714402667823478748201565 267901000433804530575587)
                    ·
                      rfl

theorem cell22_782603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 3, 1, 3].length) (baseStart_782603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_782603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_782603 prefixEnd_782603 := by exact prefixLift 782603
  have htrace : WordTrace (prefixWord ++ tailWord_782603) baseStart_782603 baseEnd_782603 := by
    simpa [prefixWord, tailWord_782603, baseEnd_782603] using wordTrace_append hprefix tailTrace_782603
  have hstable : (prefixWord ++ tailWord_782603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782603).length < 2 ^ (prefixWord ++ tailWord_782603).sum := by decide
  have hdescent : baseEnd_782603 < baseStart_782603 := by decide
  rcases family_descends (prefixWord ++ tailWord_782603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782659 : List Nat := [1, 1, 1, 3, 1, 3, 2, 4, 1, 5]
def baseStart_782659 : Nat := 118140960795 + 782659 * 2 ^ 59
def prefixEnd_782659 : Nat := 4983230072969 + 3 ^ 40 * 782659 * 2
def baseEnd_782659 : Nat := 267920170378239051175415

theorem tailTrace_782659 : CollatzResearch.WordTrace tailWord_782659 prefixEnd_782659 267920170378239051175415 := by
  unfold tailWord_782659
  simp only [CollatzResearch.WordTrace]
  refine ⟨28545918871567585360495031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19030612581045056906996687 28545918871567585360495031)
  ·
    refine ⟨42818878307351378040742547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28545918871567585360495031 42818878307351378040742547)
    ·
      refine ⟨64228317461027067061113821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42818878307351378040742547 64228317461027067061113821)
      ·
        refine ⟨24085619047885150147917683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64228317461027067061113821 24085619047885150147917683)
        ·
          refine ⟨36128428571827725221876525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24085619047885150147917683 36128428571827725221876525)
          ·
            refine ⟨13548160714435396958203697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36128428571827725221876525 13548160714435396958203697)
            ·
              refine ⟨10161120535826547718652773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13548160714435396958203697 10161120535826547718652773)
              ·
                refine ⟨1905210100467477697247395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10161120535826547718652773 1905210100467477697247395)
                ·
                  refine ⟨2857815150701216545871093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1905210100467477697247395 2857815150701216545871093)
                  ·
                    refine ⟨267920170378239051175415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2857815150701216545871093 267920170378239051175415)
                    ·
                      rfl

theorem cell22_782659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 5].length) (baseStart_782659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_782659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_782659 prefixEnd_782659 := by exact prefixLift 782659
  have htrace : WordTrace (prefixWord ++ tailWord_782659) baseStart_782659 baseEnd_782659 := by
    simpa [prefixWord, tailWord_782659, baseEnd_782659] using wordTrace_append hprefix tailTrace_782659
  have hstable : (prefixWord ++ tailWord_782659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782659).length < 2 ^ (prefixWord ++ tailWord_782659).sum := by decide
  have hdescent : baseEnd_782659 < baseStart_782659 := by decide
  rcases family_descends (prefixWord ++ tailWord_782659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782693 : List Nat := [1, 3, 1, 3, 1, 4, 1, 3, 2, 3]
def baseStart_782693 : Nat := 118140960795 + 782693 * 2 ^ 59
def prefixEnd_782693 : Nat := 4983230072969 + 3 ^ 40 * 782693 * 2
def baseEnd_782693 : Nat := 267931809273074295825311

theorem tailTrace_782693 : CollatzResearch.WordTrace tailWord_782693 prefixEnd_782693 267931809273074295825311 := by
  unfold tailWord_782693
  simp only [CollatzResearch.WordTrace]
  refine ⟨28547158953444409167232733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19031439302296272778155155 28547158953444409167232733)
  ·
    refine ⟨10705184607541653437712275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28547158953444409167232733 10705184607541653437712275)
    ·
      refine ⟨16057776911312480156568413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10705184607541653437712275 16057776911312480156568413)
      ·
        refine ⟨6021666341742180058713155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16057776911312480156568413 6021666341742180058713155)
        ·
          refine ⟨9032499512613270088069733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6021666341742180058713155 9032499512613270088069733)
          ·
            refine ⟨1693593658614988141513075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9032499512613270088069733 1693593658614988141513075)
            ·
              refine ⟨2540390487922482212269613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1693593658614988141513075 2540390487922482212269613)
              ·
                refine ⟨952646432970930829601105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2540390487922482212269613 952646432970930829601105)
                ·
                  refine ⟨714484824728198122200829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 952646432970930829601105 714484824728198122200829)
                  ·
                    refine ⟨267931809273074295825311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 714484824728198122200829 267931809273074295825311)
                    ·
                      rfl

theorem cell22_782693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 3, 2, 3].length) (baseStart_782693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_782693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_782693 prefixEnd_782693 := by exact prefixLift 782693
  have htrace : WordTrace (prefixWord ++ tailWord_782693) baseStart_782693 baseEnd_782693 := by
    simpa [prefixWord, tailWord_782693, baseEnd_782693] using wordTrace_append hprefix tailTrace_782693
  have hstable : (prefixWord ++ tailWord_782693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782693).length < 2 ^ (prefixWord ++ tailWord_782693).sum := by decide
  have hdescent : baseEnd_782693 < baseStart_782693 := by decide
  rcases family_descends (prefixWord ++ tailWord_782693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782710 : List Nat := [5, 1, 1, 4, 1, 1, 1, 2, 1, 5]
def baseStart_782710 : Nat := 118140960795 + 782710 * 2 ^ 59
def prefixEnd_782710 : Nat := 4983230072969 + 3 ^ 40 * 782710 * 2
def baseEnd_782710 : Nat := 267937628720491918150259

theorem tailTrace_782710 : CollatzResearch.WordTrace tailWord_782710 prefixEnd_782710 267937628720491918150259 := by
  unfold tailWord_782710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1784236187148926316912599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19031852662921880713734389 1784236187148926316912599)
  ·
    refine ⟨2676354280723389475368899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1784236187148926316912599 2676354280723389475368899)
    ·
      refine ⟨4014531421085084213053349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2676354280723389475368899 4014531421085084213053349)
      ·
        refine ⟨752724641453453289947503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4014531421085084213053349 752724641453453289947503)
        ·
          refine ⟨1129086962180179934921255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 752724641453453289947503 1129086962180179934921255)
          ·
            refine ⟨1693630443270269902381883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1129086962180179934921255 1693630443270269902381883)
            ·
              refine ⟨2540445664905404853572825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1693630443270269902381883 2540445664905404853572825)
              ·
                refine ⟨1905334248679053640179619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2540445664905404853572825 1905334248679053640179619)
                ·
                  refine ⟨2858001373018580460269429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1905334248679053640179619 2858001373018580460269429)
                  ·
                    refine ⟨267937628720491918150259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2858001373018580460269429 267937628720491918150259)
                    ·
                      rfl

theorem cell22_782710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_782710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_782710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_782710 prefixEnd_782710 := by exact prefixLift 782710
  have htrace : WordTrace (prefixWord ++ tailWord_782710) baseStart_782710 baseEnd_782710 := by
    simpa [prefixWord, tailWord_782710, baseEnd_782710] using wordTrace_append hprefix tailTrace_782710
  have hstable : (prefixWord ++ tailWord_782710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782710).length < 2 ^ (prefixWord ++ tailWord_782710).sum := by decide
  have hdescent : baseEnd_782710 < baseStart_782710 := by decide
  rcases family_descends (prefixWord ++ tailWord_782710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782740 : List Nat := [2, 4, 2, 1, 4, 1, 1, 7]
def baseStart_782740 : Nat := 118140960795 + 782740 * 2 ^ 59
def prefixEnd_782740 : Nat := 4983230072969 + 3 ^ 40 * 782740 * 2
def baseEnd_782740 : Nat := 29771988703731315544463

theorem tailTrace_782740 : CollatzResearch.WordTrace tailWord_782740 prefixEnd_782740 29771988703731315544463 := by
  unfold tailWord_782740
  simp only [CollatzResearch.WordTrace]
  refine ⟨14274436592137068097096837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19032582122849424129462449 14274436592137068097096837)
  ·
    refine ⟨2676456861025700268205657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14274436592137068097096837 2676456861025700268205657)
    ·
      refine ⟨2007342645769275201154243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2676456861025700268205657 2007342645769275201154243)
      ·
        refine ⟨3011013968653912801731365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2007342645769275201154243 3011013968653912801731365)
        ·
          refine ⟨564565119122608650324631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3011013968653912801731365 564565119122608650324631)
          ·
            refine ⟨846847678683912975486947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 564565119122608650324631 846847678683912975486947)
            ·
              refine ⟨1270271518025869463230421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 846847678683912975486947 1270271518025869463230421)
              ·
                refine ⟨29771988703731315544463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1270271518025869463230421 29771988703731315544463)
                ·
                  rfl

theorem cell22_782740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 7].length) (baseStart_782740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_782740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_782740 prefixEnd_782740 := by exact prefixLift 782740
  have htrace : WordTrace (prefixWord ++ tailWord_782740) baseStart_782740 baseEnd_782740 := by
    simpa [prefixWord, tailWord_782740, baseEnd_782740] using wordTrace_append hprefix tailTrace_782740
  have hstable : (prefixWord ++ tailWord_782740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782740).length < 2 ^ (prefixWord ++ tailWord_782740).sum := by decide
  have hdescent : baseEnd_782740 < baseStart_782740 := by decide
  rcases family_descends (prefixWord ++ tailWord_782740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782751 : List Nat := [1, 1, 2, 5, 1, 1, 1, 5, 5]
def baseStart_782751 : Nat := 118140960795 + 782751 * 2 ^ 59
def prefixEnd_782751 : Nat := 4983230072969 + 3 ^ 40 * 782751 * 2
def baseEnd_782751 : Nat := 89317221286127159291711

theorem tailTrace_782751 : CollatzResearch.WordTrace tailWord_782751 prefixEnd_782751 89317221286127159291711 := by
  unfold tailWord_782751
  simp only [CollatzResearch.WordTrace]
  refine ⟨28549274387234285072844107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19032849591489523381896071 28549274387234285072844107)
  ·
    refine ⟨42823911580851427609266161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28549274387234285072844107 42823911580851427609266161)
    ·
      refine ⟨32117933685638570706949621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42823911580851427609266161 32117933685638570706949621)
      ·
        refine ⟨3011056283028616003776527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32117933685638570706949621 3011056283028616003776527)
        ·
          refine ⟨4516584424542924005664791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3011056283028616003776527 4516584424542924005664791)
          ·
            refine ⟨6774876636814386008497187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4516584424542924005664791 6774876636814386008497187)
            ·
              refine ⟨10162314955221579012745781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6774876636814386008497187 10162314955221579012745781)
              ·
                refine ⟨952717027052023032444917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10162314955221579012745781 952717027052023032444917)
                ·
                  refine ⟨89317221286127159291711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 952717027052023032444917 89317221286127159291711)
                  ·
                    rfl

theorem cell22_782751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 5, 5].length) (baseStart_782751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_782751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_782751 prefixEnd_782751 := by exact prefixLift 782751
  have htrace : WordTrace (prefixWord ++ tailWord_782751) baseStart_782751 baseEnd_782751 := by
    simpa [prefixWord, tailWord_782751, baseEnd_782751] using wordTrace_append hprefix tailTrace_782751
  have hstable : (prefixWord ++ tailWord_782751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782751).length < 2 ^ (prefixWord ++ tailWord_782751).sum := by decide
  have hdescent : baseEnd_782751 < baseStart_782751 := by decide
  rcases family_descends (prefixWord ++ tailWord_782751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782802 : List Nat := [3, 2, 2, 4, 1, 1, 3, 1, 5]
def baseStart_782802 : Nat := 118140960795 + 782802 * 2 ^ 59
def prefixEnd_782802 : Nat := 4983230072969 + 3 ^ 40 * 782802 * 2
def baseEnd_782802 : Nat := 89323040733544781616659

theorem tailTrace_782802 : CollatzResearch.WordTrace tailWord_782802 prefixEnd_782802 89323040733544781616659 := by
  unfold tailWord_782802
  simp only [CollatzResearch.WordTrace]
  refine ⟨7137783627512380195737665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19034089673366347188633773 7137783627512380195737665)
  ·
    refine ⟨5353337720634285146803249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7137783627512380195737665 5353337720634285146803249)
    ·
      refine ⟨4015003290475713860102437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5353337720634285146803249 4015003290475713860102437)
      ·
        refine ⟨752813116964196348769207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4015003290475713860102437 752813116964196348769207)
        ·
          refine ⟨1129219675446294523153811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 752813116964196348769207 1129219675446294523153811)
          ·
            refine ⟨1693829513169441784730717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1129219675446294523153811 1693829513169441784730717)
            ·
              refine ⟨635186067438540669274019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1693829513169441784730717 635186067438540669274019)
              ·
                refine ⟨952779101157811003911029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 635186067438540669274019 952779101157811003911029)
                ·
                  refine ⟨89323040733544781616659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 952779101157811003911029 89323040733544781616659)
                  ·
                    rfl

theorem cell22_782802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 1, 5].length) (baseStart_782802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_782802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_782802 prefixEnd_782802 := by exact prefixLift 782802
  have htrace : WordTrace (prefixWord ++ tailWord_782802) baseStart_782802 baseEnd_782802 := by
    simpa [prefixWord, tailWord_782802, baseEnd_782802] using wordTrace_append hprefix tailTrace_782802
  have hstable : (prefixWord ++ tailWord_782802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782802).length < 2 ^ (prefixWord ++ tailWord_782802).sum := by decide
  have hdescent : baseEnd_782802 < baseStart_782802 := by decide
  rcases family_descends (prefixWord ++ tailWord_782802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782830 : List Nat := [4, 1, 2, 1, 2, 2, 3, 3, 4]
def baseStart_782830 : Nat := 118140960795 + 782830 * 2 ^ 59
def prefixEnd_782830 : Nat := 4983230072969 + 3 ^ 40 * 782830 * 2
def baseEnd_782830 : Nat := 89326235724283868383297

theorem tailTrace_782830 : CollatzResearch.WordTrace tailWord_782830 prefixEnd_782830 89326235724283868383297 := by
  unfold tailWord_782830
  simp only [CollatzResearch.WordTrace]
  refine ⟨3569019469243510195621243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19034770502632054376646629 3569019469243510195621243)
  ·
    refine ⟨5353529203865265293431865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3569019469243510195621243 5353529203865265293431865)
    ·
      refine ⟨4015146902898948970073899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5353529203865265293431865 4015146902898948970073899)
      ·
        refine ⟨6022720354348423455110849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4015146902898948970073899 6022720354348423455110849)
        ·
          refine ⟨4517040265761317591333137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6022720354348423455110849 4517040265761317591333137)
          ·
            refine ⟨3387780199320988193499853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4517040265761317591333137 3387780199320988193499853)
            ·
              refine ⟨1270417574745370572562445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3387780199320988193499853 1270417574745370572562445)
              ·
                refine ⟨476406590529513964710917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1270417574745370572562445 476406590529513964710917)
                ·
                  refine ⟨89326235724283868383297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 476406590529513964710917 89326235724283868383297)
                  ·
                    rfl

theorem cell22_782830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 3, 4].length) (baseStart_782830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_782830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_782830 prefixEnd_782830 := by exact prefixLift 782830
  have htrace : WordTrace (prefixWord ++ tailWord_782830) baseStart_782830 baseEnd_782830 := by
    simpa [prefixWord, tailWord_782830, baseEnd_782830] using wordTrace_append hprefix tailTrace_782830
  have hstable : (prefixWord ++ tailWord_782830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782830).length < 2 ^ (prefixWord ++ tailWord_782830).sum := by decide
  have hdescent : baseEnd_782830 < baseStart_782830 := by decide
  rcases family_descends (prefixWord ++ tailWord_782830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782862 : List Nat := [4, 1, 1, 2, 3, 1, 4, 1, 2, 3]
def baseStart_782862 : Nat := 118140960795 + 782862 * 2 ^ 59
def prefixEnd_782862 : Nat := 4983230072969 + 3 ^ 40 * 782862 * 2
def baseEnd_782862 : Nat := 267989661426814188349793

theorem tailTrace_782862 : CollatzResearch.WordTrace tailWord_782862 prefixEnd_782862 267989661426814188349793 := by
  unfold tailWord_782862
  simp only [CollatzResearch.WordTrace]
  refine ⟨3569165361229018878766855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19035548593221434020089893 3569165361229018878766855)
  ·
    refine ⟨5353748041843528318150283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3569165361229018878766855 5353748041843528318150283)
    ·
      refine ⟨8030622062765292477225425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5353748041843528318150283 8030622062765292477225425)
      ·
        refine ⟨6022966547073969357919069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8030622062765292477225425 6022966547073969357919069)
        ·
          refine ⟨2258612455152738509219651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6022966547073969357919069 2258612455152738509219651)
          ·
            refine ⟨3387918682729107763829477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2258612455152738509219651 3387918682729107763829477)
            ·
              refine ⟨635234753011707705718027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3387918682729107763829477 635234753011707705718027)
              ·
                refine ⟨952852129517561558577041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 635234753011707705718027 952852129517561558577041)
                ·
                  refine ⟨714639097138171168932781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 952852129517561558577041 714639097138171168932781)
                  ·
                    refine ⟨267989661426814188349793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 714639097138171168932781 267989661426814188349793)
                    ·
                      rfl

theorem cell22_782862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 1, 2, 3].length) (baseStart_782862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_782862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_782862 prefixEnd_782862 := by exact prefixLift 782862
  have htrace : WordTrace (prefixWord ++ tailWord_782862) baseStart_782862 baseEnd_782862 := by
    simpa [prefixWord, tailWord_782862, baseEnd_782862] using wordTrace_append hprefix tailTrace_782862
  have hstable : (prefixWord ++ tailWord_782862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782862).length < 2 ^ (prefixWord ++ tailWord_782862).sum := by decide
  have hdescent : baseEnd_782862 < baseStart_782862 := by decide
  rcases family_descends (prefixWord ++ tailWord_782862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782903 : List Nat := [1, 1, 3, 1, 2, 3, 4, 2, 5]
def baseStart_782903 : Nat := 118140960795 + 782903 * 2 ^ 59
def prefixEnd_782903 : Nat := 4983230072969 + 3 ^ 40 * 782903 * 2
def baseEnd_782903 : Nat := 89334565521567916024889

theorem tailTrace_782903 : CollatzResearch.WordTrace tailWord_782903 prefixEnd_782903 89334565521567916024889 := by
  unfold tailWord_782903
  simp only [CollatzResearch.WordTrace]
  refine ⟨28554818282683615032377363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19036545521789076688251575 28554818282683615032377363)
  ·
    refine ⟨42832227424025422548566045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28554818282683615032377363 42832227424025422548566045)
    ·
      refine ⟨16062085284009533455712267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42832227424025422548566045 16062085284009533455712267)
      ·
        refine ⟨24093127926014300183568401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16062085284009533455712267 24093127926014300183568401)
        ·
          refine ⟨18069845944510725137676301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24093127926014300183568401 18069845944510725137676301)
          ·
            refine ⟨6776192229191521926628613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18069845944510725137676301 6776192229191521926628613)
            ·
              refine ⟨1270536042973410361242865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6776192229191521926628613 1270536042973410361242865)
              ·
                refine ⟨952902032230057770932149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1270536042973410361242865 952902032230057770932149)
                ·
                  refine ⟨89334565521567916024889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 952902032230057770932149 89334565521567916024889)
                  ·
                    rfl

theorem cell22_782903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 2, 5].length) (baseStart_782903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_782903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_782903 prefixEnd_782903 := by exact prefixLift 782903
  have htrace : WordTrace (prefixWord ++ tailWord_782903) baseStart_782903 baseEnd_782903 := by
    simpa [prefixWord, tailWord_782903, baseEnd_782903] using wordTrace_append hprefix tailTrace_782903
  have hstable : (prefixWord ++ tailWord_782903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782903).length < 2 ^ (prefixWord ++ tailWord_782903).sum := by decide
  have hdescent : baseEnd_782903 < baseStart_782903 := by decide
  rcases family_descends (prefixWord ++ tailWord_782903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782933 : List Nat := [1, 3, 2, 2, 1, 1, 4, 1, 3, 4]
def baseStart_782933 : Nat := 118140960795 + 782933 * 2 ^ 59
def prefixEnd_782933 : Nat := 4983230072969 + 3 ^ 40 * 782933 * 2
def baseEnd_782933 : Nat := 268013966177793669824575

theorem tailTrace_782933 : CollatzResearch.WordTrace tailWord_782933 prefixEnd_782933 268013966177793669824575 := by
  unfold tailWord_782933
  simp only [CollatzResearch.WordTrace]
  refine ⟨28555912472574930155969453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19037274981716620103979635 28555912472574930155969453)
  ·
    refine ⟨10708467177215598808488545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28555912472574930155969453 10708467177215598808488545)
    ·
      refine ⟨8031350382911699106366409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10708467177215598808488545 8031350382911699106366409)
      ·
        refine ⟨6023512787183774329774807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8031350382911699106366409 6023512787183774329774807)
        ·
          refine ⟨9035269180775661494662211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6023512787183774329774807 9035269180775661494662211)
          ·
            refine ⟨13552903771163492241993317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9035269180775661494662211 13552903771163492241993317)
            ·
              refine ⟨2541169457093154795373747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13552903771163492241993317 2541169457093154795373747)
              ·
                refine ⟨3811754185639732193060621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2541169457093154795373747 3811754185639732193060621)
                ·
                  refine ⟨1429407819614899572397733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3811754185639732193060621 1429407819614899572397733)
                  ·
                    refine ⟨268013966177793669824575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1429407819614899572397733 268013966177793669824575)
                    ·
                      rfl

theorem cell22_782933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_782933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_782933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_782933 prefixEnd_782933 := by exact prefixLift 782933
  have htrace : WordTrace (prefixWord ++ tailWord_782933) baseStart_782933 baseEnd_782933 := by
    simpa [prefixWord, tailWord_782933, baseEnd_782933] using wordTrace_append hprefix tailTrace_782933
  have hstable : (prefixWord ++ tailWord_782933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782933).length < 2 ^ (prefixWord ++ tailWord_782933).sum := by decide
  have hdescent : baseEnd_782933 < baseStart_782933 := by decide
  rcases family_descends (prefixWord ++ tailWord_782933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782980 : List Nat := [2, 3, 2, 1, 3, 1, 3, 1, 1, 5]
def baseStart_782980 : Nat := 118140960795 + 782980 * 2 ^ 59
def prefixEnd_782980 : Nat := 4983230072969 + 3 ^ 40 * 782980 * 2
def baseEnd_782980 : Nat := 268030055238301213899431

theorem tailTrace_782980 : CollatzResearch.WordTrace tailWord_782980 prefixEnd_782980 268030055238301213899431 := by
  unfold tailWord_782980
  simp only [CollatzResearch.WordTrace]
  refine ⟨14278813351702328591465197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19038417802269771455286929 14278813351702328591465197)
  ·
    refine ⟨5354555006888373221799449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14278813351702328591465197 5354555006888373221799449)
    ·
      refine ⟨4015916255166279916349587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5354555006888373221799449 4015916255166279916349587)
      ·
        refine ⟨6023874382749419874524381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4015916255166279916349587 6023874382749419874524381)
        ·
          refine ⟨2258952893531032452946643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6023874382749419874524381 2258952893531032452946643)
          ·
            refine ⟨3388429340296548679419965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2258952893531032452946643 3388429340296548679419965)
            ·
              refine ⟨1270661002611205754782487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3388429340296548679419965 1270661002611205754782487)
              ·
                refine ⟨1905991503916808632173731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1270661002611205754782487 1905991503916808632173731)
                ·
                  refine ⟨2858987255875212948260597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1905991503916808632173731 2858987255875212948260597)
                  ·
                    refine ⟨268030055238301213899431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2858987255875212948260597 268030055238301213899431)
                    ·
                      rfl

theorem cell22_782980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_782980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_782980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_782980 prefixEnd_782980 := by exact prefixLift 782980
  have htrace : WordTrace (prefixWord ++ tailWord_782980) baseStart_782980 baseEnd_782980 := by
    simpa [prefixWord, tailWord_782980, baseEnd_782980] using wordTrace_append hprefix tailTrace_782980
  have hstable : (prefixWord ++ tailWord_782980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782980).length < 2 ^ (prefixWord ++ tailWord_782980).sum := by decide
  have hdescent : baseEnd_782980 < baseStart_782980 := by decide
  rcases family_descends (prefixWord ++ tailWord_782980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783031 : List Nat := [1, 1, 3, 1, 7, 1, 2, 1, 2, 3]
def baseStart_783031 : Nat := 118140960795 + 783031 * 2 ^ 59
def prefixEnd_783031 : Nat := 4983230072969 + 3 ^ 40 * 783031 * 2
def baseEnd_783031 : Nat := 268047513580554080874275

theorem tailTrace_783031 : CollatzResearch.WordTrace tailWord_783031 prefixEnd_783031 268047513580554080874275 := by
  unfold tailWord_783031
  simp only [CollatzResearch.WordTrace]
  refine ⟨28559486826219892893036947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19039657884146595262024631 28559486826219892893036947)
  ·
    refine ⟨42839230239329839339555421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28559486826219892893036947 42839230239329839339555421)
    ·
      refine ⟨16064711339748689752333283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42839230239329839339555421 16064711339748689752333283)
      ·
        refine ⟨24097067009623034628499925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16064711339748689752333283 24097067009623034628499925)
        ·
          refine ⟨564775008038039874105467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 24097067009623034628499925 564775008038039874105467)
          ·
            refine ⟨847162512057059811158201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 564775008038039874105467 847162512057059811158201)
            ·
              refine ⟨635371884042794858368651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 847162512057059811158201 635371884042794858368651)
              ·
                refine ⟨953057826064192287552977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 635371884042794858368651 953057826064192287552977)
                ·
                  refine ⟨714793369548144215664733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 953057826064192287552977 714793369548144215664733)
                  ·
                    refine ⟨268047513580554080874275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 714793369548144215664733 268047513580554080874275)
                    ·
                      rfl

theorem cell22_783031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 1, 2, 3].length) (baseStart_783031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_783031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_783031 prefixEnd_783031 := by exact prefixLift 783031
  have htrace : WordTrace (prefixWord ++ tailWord_783031) baseStart_783031 baseEnd_783031 := by
    simpa [prefixWord, tailWord_783031, baseEnd_783031] using wordTrace_append hprefix tailTrace_783031
  have hstable : (prefixWord ++ tailWord_783031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783031).length < 2 ^ (prefixWord ++ tailWord_783031).sum := by decide
  have hdescent : baseEnd_783031 < baseStart_783031 := by decide
  rcases family_descends (prefixWord ++ tailWord_783031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783046 : List Nat := [6, 1, 2, 1, 2, 1, 2, 1, 2, 4]
def baseStart_783046 : Nat := 118140960795 + 783046 * 2 ^ 59
def prefixEnd_783046 : Nat := 4983230072969 + 3 ^ 40 * 783046 * 2
def baseEnd_783046 : Nat := 268052648387099041749229

theorem tailTrace_783046 : CollatzResearch.WordTrace tailWord_783046 prefixEnd_783046 268052648387099041749229 := by
  unfold tailWord_783046
  simp only [CollatzResearch.WordTrace]
  refine ⟨892501060036423451713531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19040022614110366969888661 892501060036423451713531)
  ·
    refine ⟨1338751590054635177570297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 892501060036423451713531 1338751590054635177570297)
    ·
      refine ⟨1004063692540976383177723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1338751590054635177570297 1004063692540976383177723)
      ·
        refine ⟨1506095538811464574766585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1004063692540976383177723 1506095538811464574766585)
        ·
          refine ⟨1129571654108598431074939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1506095538811464574766585 1129571654108598431074939)
          ·
            refine ⟨1694357481162897646612409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1129571654108598431074939 1694357481162897646612409)
            ·
              refine ⟨1270768110872173234959307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1694357481162897646612409 1270768110872173234959307)
              ·
                refine ⟨1906152166308259852438961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1270768110872173234959307 1906152166308259852438961)
                ·
                  refine ⟨1429614124731194889329221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1906152166308259852438961 1429614124731194889329221)
                  ·
                    refine ⟨268052648387099041749229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1429614124731194889329221 268052648387099041749229)
                    ·
                      rfl

theorem cell22_783046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_783046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_783046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_783046 prefixEnd_783046 := by exact prefixLift 783046
  have htrace : WordTrace (prefixWord ++ tailWord_783046) baseStart_783046 baseEnd_783046 := by
    simpa [prefixWord, tailWord_783046, baseEnd_783046] using wordTrace_append hprefix tailTrace_783046
  have hstable : (prefixWord ++ tailWord_783046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783046).length < 2 ^ (prefixWord ++ tailWord_783046).sum := by decide
  have hdescent : baseEnd_783046 < baseStart_783046 := by decide
  rcases family_descends (prefixWord ++ tailWord_783046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783076 : List Nat := [2, 3, 1, 1, 1, 6, 2, 2, 1, 3]
def baseStart_783076 : Nat := 118140960795 + 783076 * 2 ^ 59
def prefixEnd_783076 : Nat := 4983230072969 + 3 ^ 40 * 783076 * 2
def baseEnd_783076 : Nat := 268062918000188963499137

theorem tailTrace_783076 : CollatzResearch.WordTrace tailWord_783076 prefixEnd_783076 268062918000188963499137 := by
  unfold tailWord_783076
  simp only [CollatzResearch.WordTrace]
  refine ⟨14280564055528432789212541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19040752074037910385616721 14280564055528432789212541)
  ·
    refine ⟨5355211520823162295954703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14280564055528432789212541 5355211520823162295954703)
    ·
      refine ⟨8032817281234743443932055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5355211520823162295954703 8032817281234743443932055)
      ·
        refine ⟨12049225921852115165898083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8032817281234743443932055 12049225921852115165898083)
        ·
          refine ⟨18073838882778172748847125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12049225921852115165898083 18073838882778172748847125)
          ·
            refine ⟨847211197630226847602209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 18073838882778172748847125 847211197630226847602209)
            ·
              refine ⟨635408398222670135701657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 847211197630226847602209 635408398222670135701657)
              ·
                refine ⟨476556298667002601776243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 635408398222670135701657 476556298667002601776243)
                ·
                  refine ⟨714834448000503902664365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 476556298667002601776243 714834448000503902664365)
                  ·
                    refine ⟨268062918000188963499137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 714834448000503902664365 268062918000188963499137)
                    ·
                      rfl

theorem cell22_783076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 2, 1, 3].length) (baseStart_783076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_783076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_783076 prefixEnd_783076 := by exact prefixLift 783076
  have htrace : WordTrace (prefixWord ++ tailWord_783076) baseStart_783076 baseEnd_783076 := by
    simpa [prefixWord, tailWord_783076, baseEnd_783076] using wordTrace_append hprefix tailTrace_783076
  have hstable : (prefixWord ++ tailWord_783076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783076).length < 2 ^ (prefixWord ++ tailWord_783076).sum := by decide
  have hdescent : baseEnd_783076 < baseStart_783076 := by decide
  rcases family_descends (prefixWord ++ tailWord_783076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783083 : List Nat := [1, 1, 1, 1, 2, 4, 1, 5, 6]
def baseStart_783083 : Nat := 118140960795 + 783083 * 2 ^ 59
def prefixEnd_783083 : Nat := 4983230072969 + 3 ^ 40 * 783083 * 2
def baseEnd_783083 : Nat := 89355104747747759524705

theorem tailTrace_783083 : CollatzResearch.WordTrace tailWord_783083 prefixEnd_783083 89355104747747759524705 := by
  unfold tailWord_783083
  simp only [CollatzResearch.WordTrace]
  refine ⟨28561383422031505773929903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19040922281354337182619935 28561383422031505773929903)
  ·
    refine ⟨42842075133047258660894855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28561383422031505773929903 42842075133047258660894855)
    ·
      refine ⟨64263112699570887991342283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42842075133047258660894855 64263112699570887991342283)
      ·
        refine ⟨96394669049356331987013425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64263112699570887991342283 96394669049356331987013425)
        ·
          refine ⟨72296001787017248990260069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96394669049356331987013425 72296001787017248990260069)
          ·
            refine ⟨13555500335065734185673763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72296001787017248990260069 13555500335065734185673763)
            ·
              refine ⟨20333250502598601278510645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13555500335065734185673763 20333250502598601278510645)
              ·
                refine ⟨1906242234618618869860373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20333250502598601278510645 1906242234618618869860373)
                ·
                  refine ⟨89355104747747759524705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1906242234618618869860373 89355104747747759524705)
                  ·
                    rfl

theorem cell22_783083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 6].length) (baseStart_783083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_783083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_783083 prefixEnd_783083 := by exact prefixLift 783083
  have htrace : WordTrace (prefixWord ++ tailWord_783083) baseStart_783083 baseEnd_783083 := by
    simpa [prefixWord, tailWord_783083, baseEnd_783083] using wordTrace_append hprefix tailTrace_783083
  have hstable : (prefixWord ++ tailWord_783083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783083).length < 2 ^ (prefixWord ++ tailWord_783083).sum := by decide
  have hdescent : baseEnd_783083 < baseStart_783083 := by decide
  rcases family_descends (prefixWord ++ tailWord_783083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783085 : List Nat := [1, 5, 1, 2, 1, 1, 1, 1, 5, 4]
def baseStart_783085 : Nat := 118140960795 + 783085 * 2 ^ 59
def prefixEnd_783085 : Nat := 4983230072969 + 3 ^ 40 * 783085 * 2
def baseEnd_783085 : Nat := 268065998884115940024109

theorem tailTrace_783085 : CollatzResearch.WordTrace tailWord_783085 prefixEnd_783085 268065998884115940024109 := by
  unfold tailWord_783085
  simp only [CollatzResearch.WordTrace]
  refine ⟨28561456368024260115502709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19040970912016173410335139 28561456368024260115502709)
  ·
    refine ⟨2677636534502274385828379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28561456368024260115502709 2677636534502274385828379)
    ·
      refine ⟨4016454801753411578742569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2677636534502274385828379 4016454801753411578742569)
      ·
        refine ⟨3012341101315058684056927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4016454801753411578742569 3012341101315058684056927)
        ·
          refine ⟨4518511651972588026085391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3012341101315058684056927 4518511651972588026085391)
          ·
            refine ⟨6777767477958882039128087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4518511651972588026085391 6777767477958882039128087)
            ·
              refine ⟨10166651216938323058692131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6777767477958882039128087 10166651216938323058692131)
              ·
                refine ⟨15249976825407484588038197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10166651216938323058692131 15249976825407484588038197)
                ·
                  refine ⟨1429685327381951680128581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15249976825407484588038197 1429685327381951680128581)
                  ·
                    refine ⟨268065998884115940024109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1429685327381951680128581 268065998884115940024109)
                    ·
                      rfl

theorem cell22_783085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_783085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_783085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_783085 prefixEnd_783085 := by exact prefixLift 783085
  have htrace : WordTrace (prefixWord ++ tailWord_783085) baseStart_783085 baseEnd_783085 := by
    simpa [prefixWord, tailWord_783085, baseEnd_783085] using wordTrace_append hprefix tailTrace_783085
  have hstable : (prefixWord ++ tailWord_783085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783085).length < 2 ^ (prefixWord ++ tailWord_783085).sum := by decide
  have hdescent : baseEnd_783085 < baseStart_783085 := by decide
  rcases family_descends (prefixWord ++ tailWord_783085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783100 : List Nat := [2, 2, 2, 1, 3, 3, 1, 2, 6]
def baseStart_783100 : Nat := 118140960795 + 783100 * 2 ^ 59
def prefixEnd_783100 : Nat := 4983230072969 + 3 ^ 40 * 783100 * 2
def baseEnd_783100 : Nat := 89357044563553633633021

theorem tailTrace_783100 : CollatzResearch.WordTrace tailWord_783100 prefixEnd_783100 89357044563553633633021 := by
  unfold tailWord_783100
  simp only [CollatzResearch.WordTrace]
  refine ⟨14281001731484958838649377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19041335641979945118199169 14281001731484958838649377)
  ·
    refine ⟨10710751298613719128987033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14281001731484958838649377 10710751298613719128987033)
    ·
      refine ⟨8033063473960289346740275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10710751298613719128987033 8033063473960289346740275)
      ·
        refine ⟨12049595210940434020110413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8033063473960289346740275 12049595210940434020110413)
        ·
          refine ⟨4518598204102662757541405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12049595210940434020110413 4518598204102662757541405)
          ·
            refine ⟨1694474326538498534078027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4518598204102662757541405 1694474326538498534078027)
            ·
              refine ⟨2541711489807747801117041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1694474326538498534078027 2541711489807747801117041)
              ·
                refine ⟨1906283617355810850837781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2541711489807747801117041 1906283617355810850837781)
                ·
                  refine ⟨89357044563553633633021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1906283617355810850837781 89357044563553633633021)
                  ·
                    rfl

theorem cell22_783100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 6].length) (baseStart_783100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_783100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_783100 prefixEnd_783100 := by exact prefixLift 783100
  have htrace : WordTrace (prefixWord ++ tailWord_783100) baseStart_783100 baseEnd_783100 := by
    simpa [prefixWord, tailWord_783100, baseEnd_783100] using wordTrace_append hprefix tailTrace_783100
  have hstable : (prefixWord ++ tailWord_783100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783100).length < 2 ^ (prefixWord ++ tailWord_783100).sum := by decide
  have hdescent : baseEnd_783100 < baseStart_783100 := by decide
  rcases family_descends (prefixWord ++ tailWord_783100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783102 : List Nat := [4, 2, 2, 1, 2, 1, 2, 1, 3, 4]
def baseStart_783102 : Nat := 118140960795 + 783102 * 2 ^ 59
def prefixEnd_783102 : Nat := 4983230072969 + 3 ^ 40 * 783102 * 2
def baseEnd_783102 : Nat := 268071818331533562349057

theorem tailTrace_783102 : CollatzResearch.WordTrace tailWord_783102 prefixEnd_783102 268071818331533562349057 := by
  unfold tailWord_783102
  simp only [CollatzResearch.WordTrace]
  refine ⟨3570259551120334002358945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19041384272641781345914373 3570259551120334002358945)
  ·
    refine ⟨2677694663340250501769209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3570259551120334002358945 2677694663340250501769209)
    ·
      refine ⟨2008270997505187876326907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2677694663340250501769209 2008270997505187876326907)
      ·
        refine ⟨3012406496257781814490361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2008270997505187876326907 3012406496257781814490361)
        ·
          refine ⟨2259304872193336360867771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3012406496257781814490361 2259304872193336360867771)
          ·
            refine ⟨3388957308290004541301657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2259304872193336360867771 3388957308290004541301657)
            ·
              refine ⟨2541717981217503405976243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3388957308290004541301657 2541717981217503405976243)
              ·
                refine ⟨3812576971826255108964365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2541717981217503405976243 3812576971826255108964365)
                ·
                  refine ⟨1429716364434845665861637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3812576971826255108964365 1429716364434845665861637)
                  ·
                    refine ⟨268071818331533562349057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1429716364434845665861637 268071818331533562349057)
                    ·
                      rfl

theorem cell22_783102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_783102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_783102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_783102 prefixEnd_783102 := by exact prefixLift 783102
  have htrace : WordTrace (prefixWord ++ tailWord_783102) baseStart_783102 baseEnd_783102 := by
    simpa [prefixWord, tailWord_783102, baseEnd_783102] using wordTrace_append hprefix tailTrace_783102
  have hstable : (prefixWord ++ tailWord_783102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783102).length < 2 ^ (prefixWord ++ tailWord_783102).sum := by decide
  have hdescent : baseEnd_783102 < baseStart_783102 := by decide
  rcases family_descends (prefixWord ++ tailWord_783102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783115 : List Nat := [1, 1, 1, 1, 5, 1, 1, 4, 4, 3]
def baseStart_783115 : Nat := 118140960795 + 783115 * 2 ^ 59
def prefixEnd_783115 : Nat := 4983230072969 + 3 ^ 40 * 783115 * 2
def baseEnd_783115 : Nat := 268076268497205861774017

theorem tailTrace_783115 : CollatzResearch.WordTrace tailWord_783115 prefixEnd_783115 268076268497205861774017 := by
  unfold tailWord_783115
  simp only [CollatzResearch.WordTrace]
  refine ⟨28562550557915575239094799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19041700371943716826063199 28562550557915575239094799)
  ·
    refine ⟨42843825836873362858642199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28562550557915575239094799 42843825836873362858642199)
    ·
      refine ⟨64265738755310044287963299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42843825836873362858642199 64265738755310044287963299)
      ·
        refine ⟨96398608132965066431944949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64265738755310044287963299 96398608132965066431944949)
        ·
          refine ⟨9037369512465474977994839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96398608132965066431944949 9037369512465474977994839)
          ·
            refine ⟨13556054268698212466992259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9037369512465474977994839 13556054268698212466992259)
            ·
              refine ⟨20334081403047318700488389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13556054268698212466992259 20334081403047318700488389)
              ·
                refine ⟨3812640263071372256341573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20334081403047318700488389 3812640263071372256341573)
                ·
                  refine ⟨714870049325882298064045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3812640263071372256341573 714870049325882298064045)
                  ·
                    refine ⟨268076268497205861774017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 714870049325882298064045 268076268497205861774017)
                    ·
                      rfl

theorem cell22_783115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 4, 3].length) (baseStart_783115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_783115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_783115 prefixEnd_783115 := by exact prefixLift 783115
  have htrace : WordTrace (prefixWord ++ tailWord_783115) baseStart_783115 baseEnd_783115 := by
    simpa [prefixWord, tailWord_783115, baseEnd_783115] using wordTrace_append hprefix tailTrace_783115
  have hstable : (prefixWord ++ tailWord_783115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783115).length < 2 ^ (prefixWord ++ tailWord_783115).sum := by decide
  have hdescent : baseEnd_783115 < baseStart_783115 := by decide
  rcases family_descends (prefixWord ++ tailWord_783115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783130 : List Nat := [3, 1, 1, 3, 2, 1, 2, 1, 4, 4]
def baseStart_783130 : Nat := 118140960795 + 783130 * 2 ^ 59
def prefixEnd_783130 : Nat := 4983230072969 + 3 ^ 40 * 783130 * 2
def baseEnd_783130 : Nat := 268081403303750822648971

theorem tailTrace_783130 : CollatzResearch.WordTrace tailWord_783130 prefixEnd_783130 268081403303750822648971 := by
  unfold tailWord_783130
  simp only [CollatzResearch.WordTrace]
  refine ⟨7140774413215308200222711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19042065101907488533927229 7140774413215308200222711)
  ·
    refine ⟨10711161619822962300334067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7140774413215308200222711 10711161619822962300334067)
    ·
      refine ⟨16066742429734443450501101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10711161619822962300334067 16066742429734443450501101)
      ·
        refine ⟨6025028411150416293937913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16066742429734443450501101 6025028411150416293937913)
        ·
          refine ⟨4518771308362812220453435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6025028411150416293937913 4518771308362812220453435)
          ·
            refine ⟨6778156962544218330680153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4518771308362812220453435 6778156962544218330680153)
            ·
              refine ⟨5083617721908163748010115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6778156962544218330680153 5083617721908163748010115)
              ·
                refine ⟨7625426582862245622015173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5083617721908163748010115 7625426582862245622015173)
                ·
                  refine ⟨1429767484286671054127845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7625426582862245622015173 1429767484286671054127845)
                  ·
                    refine ⟨268081403303750822648971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1429767484286671054127845 268081403303750822648971)
                    ·
                      rfl

theorem cell22_783130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 4, 4].length) (baseStart_783130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_783130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_783130 prefixEnd_783130 := by exact prefixLift 783130
  have htrace : WordTrace (prefixWord ++ tailWord_783130) baseStart_783130 baseEnd_783130 := by
    simpa [prefixWord, tailWord_783130, baseEnd_783130] using wordTrace_append hprefix tailTrace_783130
  have hstable : (prefixWord ++ tailWord_783130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783130).length < 2 ^ (prefixWord ++ tailWord_783130).sum := by decide
  have hdescent : baseEnd_783130 < baseStart_783130 := by decide
  rcases family_descends (prefixWord ++ tailWord_783130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783132 : List Nat := [2, 2, 3, 1, 1, 4, 1, 1, 4, 3]
def baseStart_783132 : Nat := 118140960795 + 783132 * 2 ^ 59
def prefixEnd_783132 : Nat := 4983230072969 + 3 ^ 40 * 783132 * 2
def baseEnd_783132 : Nat := 268082087944623484098965

theorem tailTrace_783132 : CollatzResearch.WordTrace tailWord_783132 prefixEnd_783132 268082087944623484098965 := by
  unfold tailWord_783132
  simp only [CollatzResearch.WordTrace]
  refine ⟨14281585299426993571231825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19042113732569324761642433 14281585299426993571231825)
  ·
    refine ⟨10711188974570245178423869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14281585299426993571231825 10711188974570245178423869)
    ·
      refine ⟨4016695865463841941908951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10711188974570245178423869 4016695865463841941908951)
      ·
        refine ⟨6025043798195762912863427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4016695865463841941908951 6025043798195762912863427)
        ·
          refine ⟨9037565697293644369295141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6025043798195762912863427 9037565697293644369295141)
          ·
            refine ⟨1694543568242558319242839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9037565697293644369295141 1694543568242558319242839)
            ·
              refine ⟨2541815352363837478864259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1694543568242558319242839 2541815352363837478864259)
              ·
                refine ⟨3812723028545756218296389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2541815352363837478864259 3812723028545756218296389)
                ·
                  refine ⟨714885567852329290930573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3812723028545756218296389 714885567852329290930573)
                  ·
                    refine ⟨268082087944623484098965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 714885567852329290930573 268082087944623484098965)
                    ·
                      rfl

theorem cell22_783132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_783132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_783132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_783132 prefixEnd_783132 := by exact prefixLift 783132
  have htrace : WordTrace (prefixWord ++ tailWord_783132) baseStart_783132 baseEnd_783132 := by
    simpa [prefixWord, tailWord_783132, baseEnd_783132] using wordTrace_append hprefix tailTrace_783132
  have hstable : (prefixWord ++ tailWord_783132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783132).length < 2 ^ (prefixWord ++ tailWord_783132).sum := by decide
  have hdescent : baseEnd_783132 < baseStart_783132 := by decide
  rcases family_descends (prefixWord ++ tailWord_783132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783194 : List Nat := [3, 1, 1, 2, 1, 6, 1, 1, 3, 3]
def baseStart_783194 : Nat := 118140960795 + 783194 * 2 ^ 59
def prefixEnd_783194 : Nat := 4983230072969 + 3 ^ 40 * 783194 * 2
def baseEnd_783194 : Nat := 268103311811675989048775

theorem tailTrace_783194 : CollatzResearch.WordTrace tailWord_783194 prefixEnd_783194 268103311811675989048775 := by
  unfold tailWord_783194
  simp only [CollatzResearch.WordTrace]
  refine ⟨7141357981157342932805159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19043621283086247820813757 7141357981157342932805159)
  ·
    refine ⟨10712036971736014399207739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7141357981157342932805159 10712036971736014399207739)
    ·
      refine ⟨16068055457604021598811609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10712036971736014399207739 16068055457604021598811609)
      ·
        refine ⟨12051041593203016199108707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16068055457604021598811609 12051041593203016199108707)
        ·
          refine ⟨18076562389804524298663061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12051041593203016199108707 18076562389804524298663061)
          ·
            refine ⟨847338862022087076499831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 18076562389804524298663061 847338862022087076499831)
            ·
              refine ⟨1271008293033130614749747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 847338862022087076499831 1271008293033130614749747)
              ·
                refine ⟨1906512439549695922124621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1271008293033130614749747 1906512439549695922124621)
                ·
                  refine ⟨714942164831135970796733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1906512439549695922124621 714942164831135970796733)
                  ·
                    refine ⟨268103311811675989048775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 714942164831135970796733 268103311811675989048775)
                    ·
                      rfl

theorem cell22_783194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 3, 3].length) (baseStart_783194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_783194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_783194 prefixEnd_783194 := by exact prefixLift 783194
  have htrace : WordTrace (prefixWord ++ tailWord_783194) baseStart_783194 baseEnd_783194 := by
    simpa [prefixWord, tailWord_783194, baseEnd_783194] using wordTrace_append hprefix tailTrace_783194
  have hstable : (prefixWord ++ tailWord_783194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783194).length < 2 ^ (prefixWord ++ tailWord_783194).sum := by decide
  have hdescent : baseEnd_783194 < baseStart_783194 := by decide
  rcases family_descends (prefixWord ++ tailWord_783194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783205 : List Nat := [1, 3, 1, 3, 1, 1, 2, 3, 2, 5]
def baseStart_783205 : Nat := 118140960795 + 783205 * 2 ^ 59
def prefixEnd_783205 : Nat := 4983230072969 + 3 ^ 40 * 783205 * 2
def baseEnd_783205 : Nat := 268107077336475627023741

theorem tailTrace_783205 : CollatzResearch.WordTrace tailWord_783205 prefixEnd_783205 268107077336475627023741 := by
  unfold tailWord_783205
  simp only [CollatzResearch.WordTrace]
  refine ⟨28565833127589520609871069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19043888751726347073247379 28565833127589520609871069)
  ·
    refine ⟨10712187422846070228701651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28565833127589520609871069 10712187422846070228701651)
    ·
      refine ⟨16068281134269105343052477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10712187422846070228701651 16068281134269105343052477)
      ·
        refine ⟨6025605425350914503644679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16068281134269105343052477 6025605425350914503644679)
        ·
          refine ⟨9038408138026371755467019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6025605425350914503644679 9038408138026371755467019)
          ·
            refine ⟨13557612207039557633200529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9038408138026371755467019 13557612207039557633200529)
            ·
              refine ⟨10168209155279668224900397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13557612207039557633200529 10168209155279668224900397)
              ·
                refine ⟨3813078433229875584337649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10168209155279668224900397 3813078433229875584337649)
                ·
                  refine ⟨2859808824922406688253237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3813078433229875584337649 2859808824922406688253237)
                  ·
                    refine ⟨268107077336475627023741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2859808824922406688253237 268107077336475627023741)
                    ·
                      rfl

theorem cell22_783205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 5].length) (baseStart_783205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_783205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_783205 prefixEnd_783205 := by exact prefixLift 783205
  have htrace : WordTrace (prefixWord ++ tailWord_783205) baseStart_783205 baseEnd_783205 := by
    simpa [prefixWord, tailWord_783205, baseEnd_783205] using wordTrace_append hprefix tailTrace_783205
  have hstable : (prefixWord ++ tailWord_783205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783205).length < 2 ^ (prefixWord ++ tailWord_783205).sum := by decide
  have hdescent : baseEnd_783205 < baseStart_783205 := by decide
  rcases family_descends (prefixWord ++ tailWord_783205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783207 : List Nat := [1, 1, 5, 1, 2, 3, 1, 3, 5]
def baseStart_783207 : Nat := 118140960795 + 783207 * 2 ^ 59
def prefixEnd_783207 : Nat := 4983230072969 + 3 ^ 40 * 783207 * 2
def baseEnd_783207 : Nat := 89369253992449429491245

theorem tailTrace_783207 : CollatzResearch.WordTrace tailWord_783207 prefixEnd_783207 89369253992449429491245 := by
  unfold tailWord_783207
  simp only [CollatzResearch.WordTrace]
  refine ⟨28565906073582274951443875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19043937382388183300962583 28565906073582274951443875)
  ·
    refine ⟨42848859110373412427165813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28565906073582274951443875 42848859110373412427165813)
    ·
      refine ⟨4017080541597507415046795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42848859110373412427165813 4017080541597507415046795)
      ·
        refine ⟨6025620812396261122570193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4017080541597507415046795 6025620812396261122570193)
        ·
          refine ⟨4519215609297195841927645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6025620812396261122570193 4519215609297195841927645)
          ·
            refine ⟨1694705853486448440722867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4519215609297195841927645 1694705853486448440722867)
            ·
              refine ⟨2542058780229672661084301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1694705853486448440722867 2542058780229672661084301)
              ·
                refine ⟨953272042586127247906613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2542058780229672661084301 953272042586127247906613)
                ·
                  refine ⟨89369253992449429491245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 953272042586127247906613 89369253992449429491245)
                  ·
                    rfl

theorem cell22_783207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 3, 5].length) (baseStart_783207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_783207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_783207 prefixEnd_783207 := by exact prefixLift 783207
  have htrace : WordTrace (prefixWord ++ tailWord_783207) baseStart_783207 baseEnd_783207 := by
    simpa [prefixWord, tailWord_783207, baseEnd_783207] using wordTrace_append hprefix tailTrace_783207
  have hstable : (prefixWord ++ tailWord_783207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783207).length < 2 ^ (prefixWord ++ tailWord_783207).sum := by decide
  have hdescent : baseEnd_783207 < baseStart_783207 := by decide
  rcases family_descends (prefixWord ++ tailWord_783207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783252 : List Nat := [2, 4, 2, 1, 1, 1, 2, 3, 6]
def baseStart_783252 : Nat := 118140960795 + 783252 * 2 ^ 59
def prefixEnd_783252 : Nat := 4983230072969 + 3 ^ 40 * 783252 * 2
def baseEnd_783252 : Nat := 89374388798994390366199

theorem tailTrace_783252 : CollatzResearch.WordTrace tailWord_783252 prefixEnd_783252 89374388798994390366199 := by
  unfold tailWord_783252
  simp only [CollatzResearch.WordTrace]
  refine ⟨14283773679209623818416005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19045031572279498424554673 14283773679209623818416005)
  ·
    refine ⟨2678207564851804465953001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14283773679209623818416005 2678207564851804465953001)
    ·
      refine ⟨2008655673638853349464751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2678207564851804465953001 2008655673638853349464751)
      ·
        refine ⟨3012983510458280024197127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2008655673638853349464751 3012983510458280024197127)
        ·
          refine ⟨4519475265687420036295691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3012983510458280024197127 4519475265687420036295691)
          ·
            refine ⟨6779212898531130054443537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4519475265687420036295691 6779212898531130054443537)
            ·
              refine ⟨5084409673898347540832653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6779212898531130054443537 5084409673898347540832653)
              ·
                refine ⟨1906653627711880327812245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5084409673898347540832653 1906653627711880327812245)
                ·
                  refine ⟨89374388798994390366199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1906653627711880327812245 89374388798994390366199)
                  ·
                    rfl

theorem cell22_783252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_783252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_783252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_783252 prefixEnd_783252 := by exact prefixLift 783252
  have htrace : WordTrace (prefixWord ++ tailWord_783252) baseStart_783252 baseEnd_783252 := by
    simpa [prefixWord, tailWord_783252, baseEnd_783252] using wordTrace_append hprefix tailTrace_783252
  have hstable : (prefixWord ++ tailWord_783252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783252).length < 2 ^ (prefixWord ++ tailWord_783252).sum := by decide
  have hdescent : baseEnd_783252 < baseStart_783252 := by decide
  rcases family_descends (prefixWord ++ tailWord_783252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783404 : List Nat := [2, 2, 1, 1, 1, 2, 4, 5, 4]
def baseStart_783404 : Nat := 118140960795 + 783404 * 2 ^ 59
def prefixEnd_783404 : Nat := 4983230072969 + 3 ^ 40 * 783404 * 2
def baseEnd_783404 : Nat := 89391733034435147099377

theorem tailTrace_783404 : CollatzResearch.WordTrace tailWord_783404 prefixEnd_783404 89391733034435147099377 := by
  unfold tailWord_783404
  simp only [CollatzResearch.WordTrace]
  refine ⟨14286545626934288798182633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19048727502579051730910177 14286545626934288798182633)
  ·
    refine ⟨10714909220200716598636975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14286545626934288798182633 10714909220200716598636975)
    ·
      refine ⟨16072363830301074897955463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10714909220200716598636975 16072363830301074897955463)
      ·
        refine ⟨24108545745451612346933195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16072363830301074897955463 24108545745451612346933195)
        ·
          refine ⟨36162818618177418520399793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24108545745451612346933195 36162818618177418520399793)
          ·
            refine ⟨27122113963633063890299845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36162818618177418520399793 27122113963633063890299845)
            ·
              refine ⟨5085396368181199479431221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27122113963633063890299845 5085396368181199479431221)
              ·
                refine ⟨476755909516987451196677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5085396368181199479431221 476755909516987451196677)
                ·
                  refine ⟨89391733034435147099377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 476755909516987451196677 89391733034435147099377)
                  ·
                    rfl

theorem cell22_783404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 5, 4].length) (baseStart_783404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_783404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_783404 prefixEnd_783404 := by exact prefixLift 783404
  have htrace : WordTrace (prefixWord ++ tailWord_783404) baseStart_783404 baseEnd_783404 := by
    simpa [prefixWord, tailWord_783404, baseEnd_783404] using wordTrace_append hprefix tailTrace_783404
  have hstable : (prefixWord ++ tailWord_783404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783404).length < 2 ^ (prefixWord ++ tailWord_783404).sum := by decide
  have hdescent : baseEnd_783404 < baseStart_783404 := by decide
  rcases family_descends (prefixWord ++ tailWord_783404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783421 : List Nat := [1, 4, 1, 3, 1, 3, 1, 4, 4]
def baseStart_783421 : Nat := 118140960795 + 783421 * 2 ^ 59
def prefixEnd_783421 : Nat := 4983230072969 + 3 ^ 40 * 783421 * 2
def baseEnd_783421 : Nat := 89393672850241021207693

theorem tailTrace_783421 : CollatzResearch.WordTrace tailWord_783421 prefixEnd_783421 89393672850241021207693 := by
  unfold tailWord_783421
  simp only [CollatzResearch.WordTrace]
  refine ⟨28573711294806989499734117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19049140863204659666489411 28573711294806989499734117)
  ·
    refine ⟨5357570867776310531200147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28573711294806989499734117 5357570867776310531200147)
    ·
      refine ⟨8036356301664465796800221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5357570867776310531200147 8036356301664465796800221)
      ·
        refine ⟨3013633613124174673800083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8036356301664465796800221 3013633613124174673800083)
        ·
          refine ⟨4520450419686262010700125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3013633613124174673800083 4520450419686262010700125)
          ·
            refine ⟨1695168907382348254012547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4520450419686262010700125 1695168907382348254012547)
            ·
              refine ⟨2542753361073522381018821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1695168907382348254012547 2542753361073522381018821)
              ·
                refine ⟨476766255201285446441029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2542753361073522381018821 476766255201285446441029)
                ·
                  refine ⟨89393672850241021207693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 476766255201285446441029 89393672850241021207693)
                  ·
                    rfl

theorem cell22_783421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 4, 4].length) (baseStart_783421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_783421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_783421 prefixEnd_783421 := by exact prefixLift 783421
  have htrace : WordTrace (prefixWord ++ tailWord_783421) baseStart_783421 baseEnd_783421 := by
    simpa [prefixWord, tailWord_783421, baseEnd_783421] using wordTrace_append hprefix tailTrace_783421
  have hstable : (prefixWord ++ tailWord_783421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783421).length < 2 ^ (prefixWord ++ tailWord_783421).sum := by decide
  have hdescent : baseEnd_783421 < baseStart_783421 := by decide
  rcases family_descends (prefixWord ++ tailWord_783421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783539 : List Nat := [1, 1, 1, 2, 3, 2, 5, 1, 6]
def baseStart_783539 : Nat := 118140960795 + 783539 * 2 ^ 59
def prefixEnd_783539 : Nat := 4983230072969 + 3 ^ 40 * 783539 * 2
def baseEnd_783539 : Nat := 89407137454070029724239

theorem tailTrace_783539 : CollatzResearch.WordTrace tailWord_783539 prefixEnd_783539 89407137454070029724239 := by
  unfold tailWord_783539
  simp only [CollatzResearch.WordTrace]
  refine ⟨28578015108379495652529671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19052010072252997101686447 28578015108379495652529671)
  ·
    refine ⟨42867022662569243478794507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28578015108379495652529671 42867022662569243478794507)
    ·
      refine ⟨64300533993853865218191761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42867022662569243478794507 64300533993853865218191761)
      ·
        refine ⟨48225400495390398913643821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64300533993853865218191761 48225400495390398913643821)
        ·
          refine ⟨18084525185771399592616433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48225400495390398913643821 18084525185771399592616433)
          ·
            refine ⟨13563393889328549694462325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18084525185771399592616433 13563393889328549694462325)
            ·
              refine ⟨1271568177124551533855843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13563393889328549694462325 1271568177124551533855843)
              ·
                refine ⟨1907352265686827300783765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1271568177124551533855843 1907352265686827300783765)
                ·
                  refine ⟨89407137454070029724239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1907352265686827300783765 89407137454070029724239)
                  ·
                    rfl

theorem cell22_783539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 6].length) (baseStart_783539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_783539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_783539 prefixEnd_783539 := by exact prefixLift 783539
  have htrace : WordTrace (prefixWord ++ tailWord_783539) baseStart_783539 baseEnd_783539 := by
    simpa [prefixWord, tailWord_783539, baseEnd_783539] using wordTrace_append hprefix tailTrace_783539
  have hstable : (prefixWord ++ tailWord_783539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783539).length < 2 ^ (prefixWord ++ tailWord_783539).sum := by decide
  have hdescent : baseEnd_783539 < baseStart_783539 := by decide
  rcases family_descends (prefixWord ++ tailWord_783539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783650 : List Nat := [3, 3, 1, 1, 4, 1, 2, 1, 3, 3]
def baseStart_783650 : Nat := 118140960795 + 783650 * 2 ^ 59
def prefixEnd_783650 : Nat := 4983230072969 + 3 ^ 40 * 783650 * 2
def baseEnd_783650 : Nat := 268259409930642799647377

theorem tailTrace_783650 : CollatzResearch.WordTrace tailWord_783650 prefixEnd_783650 268259409930642799647377 := by
  unfold tailWord_783650
  simp only [CollatzResearch.WordTrace]
  refine ⟨7145515902744340402455101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19054709073984907739880269 7145515902744340402455101)
  ·
    refine ⟨2679568463529127650920663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7145515902744340402455101 2679568463529127650920663)
    ·
      refine ⟨4019352695293691476380995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2679568463529127650920663 4019352695293691476380995)
      ·
        refine ⟨6029029042940537214571493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4019352695293691476380995 6029029042940537214571493)
        ·
          refine ⟨1130442945551350727732155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6029029042940537214571493 1130442945551350727732155)
          ·
            refine ⟨1695664418327026091598233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1130442945551350727732155 1695664418327026091598233)
            ·
              refine ⟨1271748313745269568698675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1695664418327026091598233 1271748313745269568698675)
              ·
                refine ⟨1907622470617904353048013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1271748313745269568698675 1907622470617904353048013)
                ·
                  refine ⟨715358426481714132393005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1907622470617904353048013 715358426481714132393005)
                  ·
                    refine ⟨268259409930642799647377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 715358426481714132393005 268259409930642799647377)
                    ·
                      rfl

theorem cell22_783650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_783650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_783650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_783650 prefixEnd_783650 := by exact prefixLift 783650
  have htrace : WordTrace (prefixWord ++ tailWord_783650) baseStart_783650 baseEnd_783650 := by
    simpa [prefixWord, tailWord_783650, baseEnd_783650] using wordTrace_append hprefix tailTrace_783650
  have hstable : (prefixWord ++ tailWord_783650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783650).length < 2 ^ (prefixWord ++ tailWord_783650).sum := by decide
  have hdescent : baseEnd_783650 < baseStart_783650 := by decide
  rcases family_descends (prefixWord ++ tailWord_783650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783684 : List Nat := [2, 3, 4, 1, 1, 3, 1, 3, 1, 3]
def baseStart_783684 : Nat := 118140960795 + 783684 * 2 ^ 59
def prefixEnd_783684 : Nat := 4983230072969 + 3 ^ 40 * 783684 * 2
def baseEnd_783684 : Nat := 268271048825478044297273

theorem tailTrace_783684 : CollatzResearch.WordTrace tailWord_783684 prefixEnd_783684 268271048825478044297273 := by
  unfold tailWord_783684
  simp only [CollatzResearch.WordTrace]
  refine ⟨14291651846427092708279053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19055535795236123611038737 14291651846427092708279053)
  ·
    refine ⟨5359369442410159765604645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14291651846427092708279053 5359369442410159765604645)
    ·
      refine ⟨1004881770451904956050871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5359369442410159765604645 1004881770451904956050871)
      ·
        refine ⟨1507322655677857434076307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1004881770451904956050871 1507322655677857434076307)
        ·
          refine ⟨2260983983516786151114461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1507322655677857434076307 2260983983516786151114461)
          ·
            refine ⟨847868993818794806667923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2260983983516786151114461 847868993818794806667923)
            ·
              refine ⟨1271803490728192210001885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 847868993818794806667923 1271803490728192210001885)
              ·
                refine ⟨476926309023072078750707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1271803490728192210001885 476926309023072078750707)
                ·
                  refine ⟨715389463534608118126061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 476926309023072078750707 715389463534608118126061)
                  ·
                    refine ⟨268271048825478044297273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 715389463534608118126061 268271048825478044297273)
                    ·
                      rfl

theorem cell22_783684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_783684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_783684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_783684 prefixEnd_783684 := by exact prefixLift 783684
  have htrace : WordTrace (prefixWord ++ tailWord_783684) baseStart_783684 baseEnd_783684 := by
    simpa [prefixWord, tailWord_783684, baseEnd_783684] using wordTrace_append hprefix tailTrace_783684
  have hstable : (prefixWord ++ tailWord_783684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783684).length < 2 ^ (prefixWord ++ tailWord_783684).sum := by decide
  have hdescent : baseEnd_783684 < baseStart_783684 := by decide
  rcases family_descends (prefixWord ++ tailWord_783684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783830 : List Nat := [5, 2, 1, 1, 1, 2, 2, 1, 2, 5]
def baseStart_783830 : Nat := 118140960795 + 783830 * 2 ^ 59
def prefixEnd_783830 : Nat := 4983230072969 + 3 ^ 40 * 783830 * 2
def baseEnd_783830 : Nat := 268321027609182330146825

theorem tailTrace_783830 : CollatzResearch.WordTrace tailWord_783830 prefixEnd_783830 268321027609182330146825 := by
  unfold tailWord_783830
  simp only [CollatzResearch.WordTrace]
  refine ⟨1786789296895328271960809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19059085833550168234248629 1786789296895328271960809)
  ·
    refine ⟨1340091972671496203970607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1786789296895328271960809 1340091972671496203970607)
    ·
      refine ⟨2010137959007244305955911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1340091972671496203970607 2010137959007244305955911)
      ·
        refine ⟨3015206938510866458933867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2010137959007244305955911 3015206938510866458933867)
        ·
          refine ⟨4522810407766299688400801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3015206938510866458933867 4522810407766299688400801)
          ·
            refine ⟨3392107805824724766300601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4522810407766299688400801 3392107805824724766300601)
            ·
              refine ⟨2544080854368543574725451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3392107805824724766300601 2544080854368543574725451)
              ·
                refine ⟨3816121281552815362088177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2544080854368543574725451 3816121281552815362088177)
                ·
                  refine ⟨2862090961164611521566133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3816121281552815362088177 2862090961164611521566133)
                  ·
                    refine ⟨268321027609182330146825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2862090961164611521566133 268321027609182330146825)
                    ·
                      rfl

theorem cell22_783830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_783830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_783830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_783830 prefixEnd_783830 := by exact prefixLift 783830
  have htrace : WordTrace (prefixWord ++ tailWord_783830) baseStart_783830 baseEnd_783830 := by
    simpa [prefixWord, tailWord_783830, baseEnd_783830] using wordTrace_append hprefix tailTrace_783830
  have hstable : (prefixWord ++ tailWord_783830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783830).length < 2 ^ (prefixWord ++ tailWord_783830).sum := by decide
  have hdescent : baseEnd_783830 < baseStart_783830 := by decide
  rcases family_descends (prefixWord ++ tailWord_783830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783843 : List Nat := [1, 1, 1, 6, 2, 1, 2, 2, 6]
def baseStart_783843 : Nat := 118140960795 + 783843 * 2 ^ 59
def prefixEnd_783843 : Nat := 4983230072969 + 3 ^ 40 * 783843 * 2
def baseEnd_783843 : Nat := 89441825924951543190595

theorem tailTrace_783843 : CollatzResearch.WordTrace tailWord_783843 prefixEnd_783843 89441825924951543190595 := by
  unfold tailWord_783843
  simp only [CollatzResearch.WordTrace]
  refine ⟨28589102899278155571596183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19059401932852103714397455 28589102899278155571596183)
  ·
    refine ⟨42883654348917233357394275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28589102899278155571596183 42883654348917233357394275)
    ·
      refine ⟨64325481523375850036091413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42883654348917233357394275 64325481523375850036091413)
      ·
        refine ⟨3015256946408242970441785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 64325481523375850036091413 3015256946408242970441785)
        ·
          refine ⟨2261442709806182227831339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3015256946408242970441785 2261442709806182227831339)
          ·
            refine ⟨3392164064709273341747009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2261442709806182227831339 3392164064709273341747009)
            ·
              refine ⟨2544123048531955006310257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3392164064709273341747009 2544123048531955006310257)
              ·
                refine ⟨1908092286398966254732693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2544123048531955006310257 1908092286398966254732693)
                ·
                  refine ⟨89441825924951543190595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1908092286398966254732693 89441825924951543190595)
                  ·
                    rfl

theorem cell22_783843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 6].length) (baseStart_783843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_783843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_783843 prefixEnd_783843 := by exact prefixLift 783843
  have htrace : WordTrace (prefixWord ++ tailWord_783843) baseStart_783843 baseEnd_783843 := by
    simpa [prefixWord, tailWord_783843, baseEnd_783843] using wordTrace_append hprefix tailTrace_783843
  have hstable : (prefixWord ++ tailWord_783843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783843).length < 2 ^ (prefixWord ++ tailWord_783843).sum := by decide
  have hdescent : baseEnd_783843 < baseStart_783843 := by decide
  rcases family_descends (prefixWord ++ tailWord_783843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783845 : List Nat := [1, 3, 1, 5, 1, 1, 1, 4, 1, 4]
def baseStart_783845 : Nat := 118140960795 + 783845 * 2 ^ 59
def prefixEnd_783845 : Nat := 4983230072969 + 3 ^ 40 * 783845 * 2
def baseEnd_783845 : Nat := 268326162415727291021779

theorem tailTrace_783845 : CollatzResearch.WordTrace tailWord_783845 prefixEnd_783845 268326162415727291021779 := by
  unfold tailWord_783845
  simp only [CollatzResearch.WordTrace]
  refine ⟨28589175845270909913168989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19059450563513939942112659 28589175845270909913168989)
  ·
    refine ⟨10720940941976591217438371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28589175845270909913168989 10720940941976591217438371)
    ·
      refine ⟨16081411412964886826157557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10720940941976591217438371 16081411412964886826157557)
      ·
        refine ⟨1507632319965458139952271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16081411412964886826157557 1507632319965458139952271)
        ·
          refine ⟨2261448479948187209928407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1507632319965458139952271 2261448479948187209928407)
          ·
            refine ⟨3392172719922280814892611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2261448479948187209928407 3392172719922280814892611)
            ·
              refine ⟨5088259079883421222338917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3392172719922280814892611 5088259079883421222338917)
              ·
                refine ⟨954048577478141479188547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5088259079883421222338917 954048577478141479188547)
                ·
                  refine ⟨1431072866217212218782821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 954048577478141479188547 1431072866217212218782821)
                  ·
                    refine ⟨268326162415727291021779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1431072866217212218782821 268326162415727291021779)
                    ·
                      rfl

theorem cell22_783845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 4, 1, 4].length) (baseStart_783845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_783845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_783845 prefixEnd_783845 := by exact prefixLift 783845
  have htrace : WordTrace (prefixWord ++ tailWord_783845) baseStart_783845 baseEnd_783845 := by
    simpa [prefixWord, tailWord_783845, baseEnd_783845] using wordTrace_append hprefix tailTrace_783845
  have hstable : (prefixWord ++ tailWord_783845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783845).length < 2 ^ (prefixWord ++ tailWord_783845).sum := by decide
  have hdescent : baseEnd_783845 < baseStart_783845 := by decide
  rcases family_descends (prefixWord ++ tailWord_783845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783948 : List Nat := [2, 2, 1, 3, 1, 3, 1, 1, 1, 7]
def baseStart_783948 : Nat := 118140960795 + 783948 * 2 ^ 59
def prefixEnd_783948 : Nat := 4983230072969 + 3 ^ 40 * 783948 * 2
def baseEnd_783948 : Nat := 268361421420669355696463

theorem tailTrace_783948 : CollatzResearch.WordTrace tailWord_783948 prefixEnd_783948 268361421420669355696463 := by
  unfold tailWord_783948
  simp only [CollatzResearch.WordTrace]
  refine ⟨14296466281948879252084249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19061955042598505669445665 14296466281948879252084249)
  ·
    refine ⟨10722349711461659439063187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14296466281948879252084249 10722349711461659439063187)
    ·
      refine ⟨16083524567192489158594781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10722349711461659439063187 16083524567192489158594781)
      ·
        refine ⟨6031321712697183434473043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16083524567192489158594781 6031321712697183434473043)
        ·
          refine ⟨9046982569045775151709565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6031321712697183434473043 9046982569045775151709565)
          ·
            refine ⟨3392618463392165681891087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9046982569045775151709565 3392618463392165681891087)
            ·
              refine ⟨5088927695088248522836631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3392618463392165681891087 5088927695088248522836631)
              ·
                refine ⟨7633391542632372784254947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5088927695088248522836631 7633391542632372784254947)
                ·
                  refine ⟨11450087313948559176382421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7633391542632372784254947 11450087313948559176382421)
                  ·
                    refine ⟨268361421420669355696463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11450087313948559176382421 268361421420669355696463)
                    ·
                      rfl

theorem cell22_783948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 1, 7].length) (baseStart_783948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_783948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_783948 prefixEnd_783948 := by exact prefixLift 783948
  have htrace : WordTrace (prefixWord ++ tailWord_783948) baseStart_783948 baseEnd_783948 := by
    simpa [prefixWord, tailWord_783948, baseEnd_783948] using wordTrace_append hprefix tailTrace_783948
  have hstable : (prefixWord ++ tailWord_783948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783948).length < 2 ^ (prefixWord ++ tailWord_783948).sum := by decide
  have hdescent : baseEnd_783948 < baseStart_783948 := by decide
  rcases family_descends (prefixWord ++ tailWord_783948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783958 : List Nat := [5, 2, 2, 2, 2, 1, 1, 1, 2, 4]
def baseStart_783958 : Nat := 118140960795 + 783958 * 2 ^ 59
def prefixEnd_783958 : Nat := 4983230072969 + 3 ^ 40 * 783958 * 2
def baseEnd_783958 : Nat := 268364844625032662946433

theorem tailTrace_783958 : CollatzResearch.WordTrace tailWord_783958 prefixEnd_783958 268364844625032662946433 := by
  unfold tailWord_783958
  simp only [CollatzResearch.WordTrace]
  refine ⟨1787081080866345638252033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19062198195907686808021685 1787081080866345638252033)
  ·
    refine ⟨1340310810649759228689025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1787081080866345638252033 1340310810649759228689025)
    ·
      refine ⟨1005233107987319421516769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1340310810649759228689025 1005233107987319421516769)
      ·
        refine ⟨753924830990489566137577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1005233107987319421516769 753924830990489566137577)
        ·
          refine ⟨565443623242867174603183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 753924830990489566137577 565443623242867174603183)
          ·
            refine ⟨848165434864300761904775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 565443623242867174603183 848165434864300761904775)
            ·
              refine ⟨1272248152296451142857163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 848165434864300761904775 1272248152296451142857163)
              ·
                refine ⟨1908372228444676714285745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1272248152296451142857163 1908372228444676714285745)
                ·
                  refine ⟨1431279171333507535714309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1908372228444676714285745 1431279171333507535714309)
                  ·
                    refine ⟨268364844625032662946433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1431279171333507535714309 268364844625032662946433)
                    ·
                      rfl

theorem cell22_783958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_783958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_783958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_783958 prefixEnd_783958 := by exact prefixLift 783958
  have htrace : WordTrace (prefixWord ++ tailWord_783958) baseStart_783958 baseEnd_783958 := by
    simpa [prefixWord, tailWord_783958, baseEnd_783958] using wordTrace_append hprefix tailTrace_783958
  have hstable : (prefixWord ++ tailWord_783958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783958).length < 2 ^ (prefixWord ++ tailWord_783958).sum := by decide
  have hdescent : baseEnd_783958 < baseStart_783958 := by decide
  rcases family_descends (prefixWord ++ tailWord_783958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_783995 : List Nat := [1, 1, 1, 1, 1, 4, 3, 6, 4]
def baseStart_783995 : Nat := 118140960795 + 783995 * 2 ^ 59
def prefixEnd_783995 : Nat := 4983230072969 + 3 ^ 40 * 783995 * 2
def baseEnd_783995 : Nat := 89459170160392299923773

theorem tailTrace_783995 : CollatzResearch.WordTrace tailWord_783995 prefixEnd_783995 89459170160392299923773 := by
  unfold tailWord_783995
  simp only [CollatzResearch.WordTrace]
  refine ⟨28594646794727485531129439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19063097863151657020752959 28594646794727485531129439)
  ·
    refine ⟨42891970192091228296694159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28594646794727485531129439 42891970192091228296694159)
    ·
      refine ⟨64337955288136842445041239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42891970192091228296694159 64337955288136842445041239)
      ·
        refine ⟨96506932932205263667561859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64337955288136842445041239 96506932932205263667561859)
        ·
          refine ⟨144760399398307895501342789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96506932932205263667561859 144760399398307895501342789)
          ·
            refine ⟨27142574887182730406501773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 144760399398307895501342789 27142574887182730406501773)
            ·
              refine ⟨10178465582693523902438165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27142574887182730406501773 10178465582693523902438165)
              ·
                refine ⟨477115574188758932926789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10178465582693523902438165 477115574188758932926789)
                ·
                  refine ⟨89459170160392299923773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 477115574188758932926789 89459170160392299923773)
                  ·
                    rfl

theorem cell22_783995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 4].length) (baseStart_783995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_783995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_783995 prefixEnd_783995 := by exact prefixLift 783995
  have htrace : WordTrace (prefixWord ++ tailWord_783995) baseStart_783995 baseEnd_783995 := by
    simpa [prefixWord, tailWord_783995, baseEnd_783995] using wordTrace_append hprefix tailTrace_783995
  have hstable : (prefixWord ++ tailWord_783995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_783995).length < 2 ^ (prefixWord ++ tailWord_783995).sum := by decide
  have hdescent : baseEnd_783995 < baseStart_783995 := by decide
  rcases family_descends (prefixWord ++ tailWord_783995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784046 : List Nat := [4, 1, 4, 1, 3, 1, 1, 1, 6]
def baseStart_784046 : Nat := 118140960795 + 784046 * 2 ^ 59
def prefixEnd_784046 : Nat := 4983230072969 + 3 ^ 40 * 784046 * 2
def baseEnd_784046 : Nat := 89464989607809922248721

theorem tailTrace_784046 : CollatzResearch.WordTrace tailWord_784046 prefixEnd_784046 89464989607809922248721 := by
  unfold tailWord_784046
  simp only [CollatzResearch.WordTrace]
  refine ⟨3574563364692840155154499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19064337945028480827490661 3574563364692840155154499)
  ·
    refine ⟨5361845047039260232731749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3574563364692840155154499 5361845047039260232731749)
    ·
      refine ⟨1005345946319861293637203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5361845047039260232731749 1005345946319861293637203)
      ·
        refine ⟨1508018919479791940455805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1005345946319861293637203 1508018919479791940455805)
        ·
          refine ⟨565507094804921977670927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1508018919479791940455805 565507094804921977670927)
          ·
            refine ⟨848260642207382966506391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 565507094804921977670927 848260642207382966506391)
            ·
              refine ⟨1272390963311074449759587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 848260642207382966506391 1272390963311074449759587)
              ·
                refine ⟨1908586444966611674639381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1272390963311074449759587 1908586444966611674639381)
                ·
                  refine ⟨89464989607809922248721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1908586444966611674639381 89464989607809922248721)
                  ·
                    rfl

theorem cell22_784046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 6].length) (baseStart_784046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_784046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_784046 prefixEnd_784046 := by exact prefixLift 784046
  have htrace : WordTrace (prefixWord ++ tailWord_784046) baseStart_784046 baseEnd_784046 := by
    simpa [prefixWord, tailWord_784046, baseEnd_784046] using wordTrace_append hprefix tailTrace_784046
  have hstable : (prefixWord ++ tailWord_784046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784046).length < 2 ^ (prefixWord ++ tailWord_784046).sum := by decide
  have hdescent : baseEnd_784046 < baseStart_784046 := by decide
  rcases family_descends (prefixWord ++ tailWord_784046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784100 : List Nat := [2, 3, 1, 1, 1, 3, 2, 2, 2, 5]
def baseStart_784100 : Nat := 118140960795 + 784100 * 2 ^ 59
def prefixEnd_784100 : Nat := 4983230072969 + 3 ^ 40 * 784100 * 2
def baseEnd_784100 : Nat := 268413454126991625895997

theorem tailTrace_784100 : CollatzResearch.WordTrace tailWord_784100 prefixEnd_784100 268413454126991625895997 := by
  unfold tailWord_784100
  simp only [CollatzResearch.WordTrace]
  refine ⟨14299238229673544231850877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19065650972898058975801169 14299238229673544231850877)
  ·
    refine ⟨5362214336127579086944079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14299238229673544231850877 5362214336127579086944079)
    ·
      refine ⟨8043321504191368630416119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5362214336127579086944079 8043321504191368630416119)
      ·
        refine ⟨12064982256287052945624179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8043321504191368630416119 12064982256287052945624179)
        ·
          refine ⟨18097473384430579418436269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12064982256287052945624179 18097473384430579418436269)
          ·
            refine ⟨6786552519161467281913601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18097473384430579418436269 6786552519161467281913601)
            ·
              refine ⟨5089914389371100461435201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6786552519161467281913601 5089914389371100461435201)
              ·
                refine ⟨3817435792028325346076401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5089914389371100461435201 3817435792028325346076401)
                ·
                  refine ⟨2863076844021244009557301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3817435792028325346076401 2863076844021244009557301)
                  ·
                    refine ⟨268413454126991625895997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2863076844021244009557301 268413454126991625895997)
                    ·
                      rfl

theorem cell22_784100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_784100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_784100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_784100 prefixEnd_784100 := by exact prefixLift 784100
  have htrace : WordTrace (prefixWord ++ tailWord_784100) baseStart_784100 baseEnd_784100 := by
    simpa [prefixWord, tailWord_784100, baseEnd_784100] using wordTrace_append hprefix tailTrace_784100
  have hstable : (prefixWord ++ tailWord_784100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784100).length < 2 ^ (prefixWord ++ tailWord_784100).sum := by decide
  have hdescent : baseEnd_784100 < baseStart_784100 := by decide
  rcases family_descends (prefixWord ++ tailWord_784100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784106 : List Nat := [3, 1, 3, 1, 1, 1, 6, 2, 1, 3]
def baseStart_784106 : Nat := 118140960795 + 784106 * 2 ^ 59
def prefixEnd_784106 : Nat := 4983230072969 + 3 ^ 40 * 784106 * 2
def baseEnd_784106 : Nat := 268415508049609610245979

theorem tailTrace_784106 : CollatzResearch.WordTrace tailWord_784106 prefixEnd_784106 268415508049609610245979 := by
  unfold tailWord_784106
  simp only [CollatzResearch.WordTrace]
  refine ⟨7149673824331337872105043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19065796864883567658946781 7149673824331337872105043)
  ·
    refine ⟨10724510736497006808157565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7149673824331337872105043 10724510736497006808157565)
    ·
      refine ⟨4021691526186377553059087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10724510736497006808157565 4021691526186377553059087)
      ·
        refine ⟨6032537289279566329588631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4021691526186377553059087 6032537289279566329588631)
        ·
          refine ⟨9048805933919349494382947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6032537289279566329588631 9048805933919349494382947)
          ·
            refine ⟨13573208900879024241574421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9048805933919349494382947 13573208900879024241574421)
            ·
              refine ⟨636244167228704261323801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13573208900879024241574421 636244167228704261323801)
              ·
                refine ⟨477183125421528195992851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 636244167228704261323801 477183125421528195992851)
                ·
                  refine ⟨715774688132292293989277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 477183125421528195992851 715774688132292293989277)
                  ·
                    refine ⟨268415508049609610245979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 715774688132292293989277 268415508049609610245979)
                    ·
                      rfl

theorem cell22_784106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_784106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_784106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_784106 prefixEnd_784106 := by exact prefixLift 784106
  have htrace : WordTrace (prefixWord ++ tailWord_784106) baseStart_784106 baseEnd_784106 := by
    simpa [prefixWord, tailWord_784106, baseEnd_784106] using wordTrace_append hprefix tailTrace_784106
  have hstable : (prefixWord ++ tailWord_784106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784106).length < 2 ^ (prefixWord ++ tailWord_784106).sum := by decide
  have hdescent : baseEnd_784106 < baseStart_784106 := by decide
  rcases family_descends (prefixWord ++ tailWord_784106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784115 : List Nat := [1, 1, 1, 2, 2, 3, 3, 2, 3, 4]
def baseStart_784115 : Nat := 118140960795 + 784115 * 2 ^ 59
def prefixEnd_784115 : Nat := 4983230072969 + 3 ^ 40 * 784115 * 2
def baseEnd_784115 : Nat := 268418588933536586770951

theorem tailTrace_784115 : CollatzResearch.WordTrace tailWord_784115 prefixEnd_784115 268418588933536586770951 := by
  unfold tailWord_784115
  simp only [CollatzResearch.WordTrace]
  refine ⟨28599023554292746025497799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19066015702861830683665199 28599023554292746025497799)
  ·
    refine ⟨42898535331439119038246699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28599023554292746025497799 42898535331439119038246699)
    ·
      refine ⟨64347802997158678557370049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42898535331439119038246699 64347802997158678557370049)
      ·
        refine ⟨48260852247869008918027537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64347802997158678557370049 48260852247869008918027537)
        ·
          refine ⟨36195639185901756688520653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48260852247869008918027537 36195639185901756688520653)
          ·
            refine ⟨13573364694713158758195245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36195639185901756688520653 13573364694713158758195245)
            ·
              refine ⟨5090011760517434534323217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13573364694713158758195245 5090011760517434534323217)
              ·
                refine ⟨3817508820388075900742413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5090011760517434534323217 3817508820388075900742413)
                ·
                  refine ⟨1431565807645528462778405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3817508820388075900742413 1431565807645528462778405)
                  ·
                    refine ⟨268418588933536586770951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1431565807645528462778405 268418588933536586770951)
                    ·
                      rfl

theorem cell22_784115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 3, 4].length) (baseStart_784115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_784115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_784115 prefixEnd_784115 := by exact prefixLift 784115
  have htrace : WordTrace (prefixWord ++ tailWord_784115) baseStart_784115 baseEnd_784115 := by
    simpa [prefixWord, tailWord_784115, baseEnd_784115] using wordTrace_append hprefix tailTrace_784115
  have hstable : (prefixWord ++ tailWord_784115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784115).length < 2 ^ (prefixWord ++ tailWord_784115).sum := by decide
  have hdescent : baseEnd_784115 < baseStart_784115 := by decide
  rcases family_descends (prefixWord ++ tailWord_784115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784132 : List Nat := [2, 3, 2, 2, 1, 2, 2, 1, 3, 4]
def baseStart_784132 : Nat := 118140960795 + 784132 * 2 ^ 59
def prefixEnd_784132 : Nat := 4983230072969 + 3 ^ 40 * 784132 * 2
def baseEnd_784132 : Nat := 268424408380954209095899

theorem tailTrace_784132 : CollatzResearch.WordTrace tailWord_784132 prefixEnd_784132 268424408380954209095899 := by
  unfold tailWord_784132
  simp only [CollatzResearch.WordTrace]
  refine ⟨14299821797615578964433325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19066429063487438619244433 14299821797615578964433325)
  ·
    refine ⟨5362433174105842111662497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14299821797615578964433325 5362433174105842111662497)
    ·
      refine ⟨4021824880579381583746873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5362433174105842111662497 4021824880579381583746873)
      ·
        refine ⟨3016368660434536187810155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4021824880579381583746873 3016368660434536187810155)
        ·
          refine ⟨4524552990651804281715233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3016368660434536187810155 4524552990651804281715233)
          ·
            refine ⟨3393414742988853211286425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4524552990651804281715233 3393414742988853211286425)
            ·
              refine ⟨2545061057241639908464819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3393414742988853211286425 2545061057241639908464819)
              ·
                refine ⟨3817591585862459862697229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2545061057241639908464819 3817591585862459862697229)
                ·
                  refine ⟨1431596844698422448511461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3817591585862459862697229 1431596844698422448511461)
                  ·
                    refine ⟨268424408380954209095899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1431596844698422448511461 268424408380954209095899)
                    ·
                      rfl

theorem cell22_784132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_784132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_784132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_784132 prefixEnd_784132 := by exact prefixLift 784132
  have htrace : WordTrace (prefixWord ++ tailWord_784132) baseStart_784132 baseEnd_784132 := by
    simpa [prefixWord, tailWord_784132, baseEnd_784132] using wordTrace_append hprefix tailTrace_784132
  have hstable : (prefixWord ++ tailWord_784132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784132).length < 2 ^ (prefixWord ++ tailWord_784132).sum := by decide
  have hdescent : baseEnd_784132 < baseStart_784132 := by decide
  rcases family_descends (prefixWord ++ tailWord_784132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784149 : List Nat := [1, 3, 2, 1, 2, 3, 4, 1, 1, 4]
def baseStart_784149 : Nat := 118140960795 + 784149 * 2 ^ 59
def prefixEnd_784149 : Nat := 4983230072969 + 3 ^ 40 * 784149 * 2
def baseEnd_784149 : Nat := 268430227828371831420847

theorem tailTrace_784149 : CollatzResearch.WordTrace tailWord_784149 prefixEnd_784149 268430227828371831420847 := by
  unfold tailWord_784149
  simp only [CollatzResearch.WordTrace]
  refine ⟨28600263636169569832235501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19066842424113046554823667 28600263636169569832235501)
  ·
    refine ⟨10725098863563588687088313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28600263636169569832235501 10725098863563588687088313)
    ·
      refine ⟨8043824147672691515316235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10725098863563588687088313 8043824147672691515316235)
      ·
        refine ⟨12065736221509037272974353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8043824147672691515316235 12065736221509037272974353)
        ·
          refine ⟨9049302166131777954730765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12065736221509037272974353 9049302166131777954730765)
          ·
            refine ⟨3393488312299416733024037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9049302166131777954730765 3393488312299416733024037)
            ·
              refine ⟨636279058556140637442007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3393488312299416733024037 636279058556140637442007)
              ·
                refine ⟨954418587834210956163011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 636279058556140637442007 954418587834210956163011)
                ·
                  refine ⟨1431627881751316434244517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 954418587834210956163011 1431627881751316434244517)
                  ·
                    refine ⟨268430227828371831420847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1431627881751316434244517 268430227828371831420847)
                    ·
                      rfl

theorem cell22_784149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 1, 1, 4].length) (baseStart_784149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_784149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_784149 prefixEnd_784149 := by exact prefixLift 784149
  have htrace : WordTrace (prefixWord ++ tailWord_784149) baseStart_784149 baseEnd_784149 := by
    simpa [prefixWord, tailWord_784149, baseEnd_784149] using wordTrace_append hprefix tailTrace_784149
  have hstable : (prefixWord ++ tailWord_784149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784149).length < 2 ^ (prefixWord ++ tailWord_784149).sum := by decide
  have hdescent : baseEnd_784149 < baseStart_784149 := by decide
  rcases family_descends (prefixWord ++ tailWord_784149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784164 : List Nat := [2, 3, 1, 3, 2, 1, 2, 4, 4]
def baseStart_784164 : Nat := 118140960795 + 784164 * 2 ^ 59
def prefixEnd_784164 : Nat := 4983230072969 + 3 ^ 40 * 784164 * 2
def baseEnd_784164 : Nat := 89478454211638930765267

theorem tailTrace_784164 : CollatzResearch.WordTrace tailWord_784164 prefixEnd_784164 89478454211638930765267 := by
  unfold tailWord_784164
  simp only [CollatzResearch.WordTrace]
  refine ⟨14300405365557613697015773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19067207154076818262687697 14300405365557613697015773)
  ·
    refine ⟨5362652012084105136380915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14300405365557613697015773 5362652012084105136380915)
    ·
      refine ⟨8043978018126157704571373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5362652012084105136380915 8043978018126157704571373)
      ·
        refine ⟨3016491756797309139214265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8043978018126157704571373 3016491756797309139214265)
        ·
          refine ⟨2262368817597981854410699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3016491756797309139214265 2262368817597981854410699)
          ·
            refine ⟨3393553226396972781616049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2262368817597981854410699 3393553226396972781616049)
            ·
              refine ⟨2545164919797729586212037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3393553226396972781616049 2545164919797729586212037)
              ·
                refine ⟨477218422462074297414757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2545164919797729586212037 477218422462074297414757)
                ·
                  refine ⟨89478454211638930765267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 477218422462074297414757 89478454211638930765267)
                  ·
                    rfl

theorem cell22_784164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 4, 4].length) (baseStart_784164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_784164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_784164 prefixEnd_784164 := by exact prefixLift 784164
  have htrace : WordTrace (prefixWord ++ tailWord_784164) baseStart_784164 baseEnd_784164 := by
    simpa [prefixWord, tailWord_784164, baseEnd_784164] using wordTrace_append hprefix tailTrace_784164
  have hstable : (prefixWord ++ tailWord_784164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784164).length < 2 ^ (prefixWord ++ tailWord_784164).sum := by decide
  have hdescent : baseEnd_784164 < baseStart_784164 := by decide
  rcases family_descends (prefixWord ++ tailWord_784164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784179 : List Nat := [1, 1, 1, 2, 7, 2, 1, 1, 1, 5]
def baseStart_784179 : Nat := 118140960795 + 784179 * 2 ^ 59
def prefixEnd_784179 : Nat := 4983230072969 + 3 ^ 40 * 784179 * 2
def baseEnd_784179 : Nat := 268440497441461753170755

theorem tailTrace_784179 : CollatzResearch.WordTrace tailWord_784179 prefixEnd_784179 268440497441461753170755 := by
  unfold tailWord_784179
  simp only [CollatzResearch.WordTrace]
  refine ⟨28601357826060884955827591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19067571884040589970551727 28601357826060884955827591)
  ·
    refine ⟨42902036739091327433741387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28601357826060884955827591 42902036739091327433741387)
    ·
      refine ⟨64353055108636991150612081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42902036739091327433741387 64353055108636991150612081)
      ·
        refine ⟨48264791331477743362959061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64353055108636991150612081 48264791331477743362959061)
        ·
          refine ⟨1131206046831509610069353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 48264791331477743362959061 1131206046831509610069353)
          ·
            refine ⟨848404535123632207552015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1131206046831509610069353 848404535123632207552015)
            ·
              refine ⟨1272606802685448311328023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 848404535123632207552015 1272606802685448311328023)
              ·
                refine ⟨1908910204028172466992035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1272606802685448311328023 1908910204028172466992035)
                ·
                  refine ⟨2863365306042258700488053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1908910204028172466992035 2863365306042258700488053)
                  ·
                    refine ⟨268440497441461753170755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2863365306042258700488053 268440497441461753170755)
                    ·
                      rfl

theorem cell22_784179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 5].length) (baseStart_784179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_784179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_784179 prefixEnd_784179 := by exact prefixLift 784179
  have htrace : WordTrace (prefixWord ++ tailWord_784179) baseStart_784179 baseEnd_784179 := by
    simpa [prefixWord, tailWord_784179, baseEnd_784179] using wordTrace_append hprefix tailTrace_784179
  have hstable : (prefixWord ++ tailWord_784179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784179).length < 2 ^ (prefixWord ++ tailWord_784179).sum := by decide
  have hdescent : baseEnd_784179 < baseStart_784179 := by decide
  rcases family_descends (prefixWord ++ tailWord_784179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784198 : List Nat := [6, 1, 1, 2, 1, 1, 3, 3, 4]
def baseStart_784198 : Nat := 118140960795 + 784198 * 2 ^ 59
def prefixEnd_784198 : Nat := 4983230072969 + 3 ^ 40 * 784198 * 2
def baseEnd_784198 : Nat := 89482333843250678981899

theorem tailTrace_784198 : CollatzResearch.WordTrace tailWord_784198 prefixEnd_784198 89482333843250678981899 := by
  unfold tailWord_784198
  simp only [CollatzResearch.WordTrace]
  refine ⟨893814087906001600024039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19068033875328034133846165 893814087906001600024039)
  ·
    refine ⟨1340721131859002400036059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 893814087906001600024039 1340721131859002400036059)
    ·
      refine ⟨2011081697788503600054089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1340721131859002400036059 2011081697788503600054089)
      ·
        refine ⟨1508311273341377700040567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2011081697788503600054089 1508311273341377700040567)
        ·
          refine ⟨2262466910012066550060851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1508311273341377700040567 2262466910012066550060851)
          ·
            refine ⟨3393700365018099825091277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2262466910012066550060851 3393700365018099825091277)
            ·
              refine ⟨1272637636881787434409229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3393700365018099825091277 1272637636881787434409229)
              ·
                refine ⟨477239113830670287903461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1272637636881787434409229 477239113830670287903461)
                ·
                  refine ⟨89482333843250678981899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 477239113830670287903461 89482333843250678981899)
                  ·
                    rfl

theorem cell22_784198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_784198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_784198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_784198 prefixEnd_784198 := by exact prefixLift 784198
  have htrace : WordTrace (prefixWord ++ tailWord_784198) baseStart_784198 baseEnd_784198 := by
    simpa [prefixWord, tailWord_784198, baseEnd_784198] using wordTrace_append hprefix tailTrace_784198
  have hstable : (prefixWord ++ tailWord_784198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784198).length < 2 ^ (prefixWord ++ tailWord_784198).sum := by decide
  have hdescent : baseEnd_784198 < baseStart_784198 := by decide
  rcases family_descends (prefixWord ++ tailWord_784198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784224 : List Nat := [2, 1, 1, 3, 3, 2, 3, 1, 3, 3]
def baseStart_784224 : Nat := 118140960795 + 784224 * 2 ^ 59
def prefixEnd_784224 : Nat := 4983230072969 + 3 ^ 40 * 784224 * 2
def baseEnd_784224 : Nat := 268455901861096635795617

theorem tailTrace_784224 : CollatzResearch.WordTrace tailWord_784224 prefixEnd_784224 268455901861096635795617 := by
  unfold tailWord_784224
  simp only [CollatzResearch.WordTrace]
  refine ⟨14301499555448928820607863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19068666073931905094143817 14301499555448928820607863)
  ·
    refine ⟨21452249333173393230911795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14301499555448928820607863 21452249333173393230911795)
    ·
      refine ⟨32178373999760089846367693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21452249333173393230911795 32178373999760089846367693)
      ·
        refine ⟨12066890249910033692387885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32178373999760089846367693 12066890249910033692387885)
        ·
          refine ⟨4525083843716262634645457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12066890249910033692387885 4525083843716262634645457)
          ·
            refine ⟨3393812882787196975984093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4525083843716262634645457 3393812882787196975984093)
            ·
              refine ⟨1272679831045198865994035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3393812882787196975984093 1272679831045198865994035)
              ·
                refine ⟨1909019746567798298991053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1272679831045198865994035 1909019746567798298991053)
                ·
                  refine ⟨715882404962924362121645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1909019746567798298991053 715882404962924362121645)
                  ·
                    refine ⟨268455901861096635795617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 715882404962924362121645 268455901861096635795617)
                    ·
                      rfl

theorem cell22_784224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 3, 3].length) (baseStart_784224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_784224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_784224 prefixEnd_784224 := by exact prefixLift 784224
  have htrace : WordTrace (prefixWord ++ tailWord_784224) baseStart_784224 baseEnd_784224 := by
    simpa [prefixWord, tailWord_784224, baseEnd_784224] using wordTrace_append hprefix tailTrace_784224
  have hstable : (prefixWord ++ tailWord_784224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784224).length < 2 ^ (prefixWord ++ tailWord_784224).sum := by decide
  have hdescent : baseEnd_784224 < baseStart_784224 := by decide
  rcases family_descends (prefixWord ++ tailWord_784224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784235 : List Nat := [1, 1, 1, 1, 2, 2, 3, 3, 1, 7]
def baseStart_784235 : Nat := 118140960795 + 784235 * 2 ^ 59
def prefixEnd_784235 : Nat := 4983230072969 + 3 ^ 40 * 784235 * 2
def baseEnd_784235 : Nat := 268459667385896273770583

theorem tailTrace_784235 : CollatzResearch.WordTrace tailWord_784235 prefixEnd_784235 268459667385896273770583 := by
  unfold tailWord_784235
  simp only [CollatzResearch.WordTrace]
  refine ⟨28603400313858006519866159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19068933542572004346577439 28603400313858006519866159)
  ·
    refine ⟨42905100470787009779799239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28603400313858006519866159 42905100470787009779799239)
    ·
      refine ⟨64357650706180514669698859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42905100470787009779799239 64357650706180514669698859)
      ·
        refine ⟨96536476059270772004548289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64357650706180514669698859 96536476059270772004548289)
        ·
          refine ⟨72402357044453079003411217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96536476059270772004548289 72402357044453079003411217)
          ·
            refine ⟨54301767783339809252558413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72402357044453079003411217 54301767783339809252558413)
            ·
              refine ⟨20363162918752428469709405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54301767783339809252558413 20363162918752428469709405)
              ·
                refine ⟨7636186094532160676141027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20363162918752428469709405 7636186094532160676141027)
                ·
                  refine ⟨11454279141798241014211541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7636186094532160676141027 11454279141798241014211541)
                  ·
                    refine ⟨268459667385896273770583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11454279141798241014211541 268459667385896273770583)
                    ·
                      rfl

theorem cell22_784235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 7].length) (baseStart_784235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_784235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_784235 prefixEnd_784235 := by exact prefixLift 784235
  have htrace : WordTrace (prefixWord ++ tailWord_784235) baseStart_784235 baseEnd_784235 := by
    simpa [prefixWord, tailWord_784235, baseEnd_784235] using wordTrace_append hprefix tailTrace_784235
  have hstable : (prefixWord ++ tailWord_784235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784235).length < 2 ^ (prefixWord ++ tailWord_784235).sum := by decide
  have hdescent : baseEnd_784235 < baseStart_784235 := by decide
  rcases family_descends (prefixWord ++ tailWord_784235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784284 : List Nat := [2, 2, 3, 3, 1, 1, 1, 2, 3, 4]
def baseStart_784284 : Nat := 118140960795 + 784284 * 2 ^ 59
def prefixEnd_784284 : Nat := 4983230072969 + 3 ^ 40 * 784284 * 2
def baseEnd_784284 : Nat := 268476441087276479295433

theorem tailTrace_784284 : CollatzResearch.WordTrace tailWord_784284 prefixEnd_784284 268476441087276479295433 := by
  unfold tailWord_784284
  simp only [CollatzResearch.WordTrace]
  refine ⟨14302593745340243944199953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19070124993786991925599937 14302593745340243944199953)
  ·
    refine ⟨10726945309005182958149965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14302593745340243944199953 10726945309005182958149965)
    ·
      refine ⟨4022604490876943609306237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10726945309005182958149965 4022604490876943609306237)
      ·
        refine ⟨1508476684078853853489839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4022604490876943609306237 1508476684078853853489839)
        ·
          refine ⟨2262715026118280780234759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1508476684078853853489839 2262715026118280780234759)
          ·
            refine ⟨3394072539177421170352139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2262715026118280780234759 3394072539177421170352139)
            ·
              refine ⟨5091108808766131755528209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3394072539177421170352139 5091108808766131755528209)
              ·
                refine ⟨3818331606574598816646157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5091108808766131755528209 3818331606574598816646157)
                ·
                  refine ⟨1431874352465474556242309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3818331606574598816646157 1431874352465474556242309)
                  ·
                    refine ⟨268476441087276479295433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1431874352465474556242309 268476441087276479295433)
                    ·
                      rfl

theorem cell22_784284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_784284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_784284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_784284 prefixEnd_784284 := by exact prefixLift 784284
  have htrace : WordTrace (prefixWord ++ tailWord_784284) baseStart_784284 baseEnd_784284 := by
    simpa [prefixWord, tailWord_784284, baseEnd_784284] using wordTrace_append hprefix tailTrace_784284
  have hstable : (prefixWord ++ tailWord_784284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784284).length < 2 ^ (prefixWord ++ tailWord_784284).sum := by decide
  have hdescent : baseEnd_784284 < baseStart_784284 := by decide
  rcases family_descends (prefixWord ++ tailWord_784284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784312 : List Nat := [2, 1, 2, 1, 2, 3, 3, 1, 1, 6]
def baseStart_784312 : Nat := 118140960795 + 784312 * 2 ^ 59
def prefixEnd_784312 : Nat := 4983230072969 + 3 ^ 40 * 784312 * 2
def baseEnd_784312 : Nat := 268486026059493739595347

theorem tailTrace_784312 : CollatzResearch.WordTrace tailWord_784312 prefixEnd_784312 268486026059493739595347 := by
  unfold tailWord_784312
  simp only [CollatzResearch.WordTrace]
  refine ⟨14303104367289524335209595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19070805823052699113612793 14303104367289524335209595)
  ·
    refine ⟨21454656550934286502814393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14303104367289524335209595 21454656550934286502814393)
    ·
      refine ⟨16090992413200714877110795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21454656550934286502814393 16090992413200714877110795)
      ·
        refine ⟨24136488619801072315666193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16090992413200714877110795 24136488619801072315666193)
        ·
          refine ⟨18102366464850804236749645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24136488619801072315666193 18102366464850804236749645)
          ·
            refine ⟨6788387424319051588781117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18102366464850804236749645 6788387424319051588781117)
            ·
              refine ⟨2545645284119644345792919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6788387424319051588781117 2545645284119644345792919)
              ·
                refine ⟨3818467926179466518689379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2545645284119644345792919 3818467926179466518689379)
                ·
                  refine ⟨5727701889269199778034069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3818467926179466518689379 5727701889269199778034069)
                  ·
                    refine ⟨268486026059493739595347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5727701889269199778034069 268486026059493739595347)
                    ·
                      rfl

theorem cell22_784312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 1, 6].length) (baseStart_784312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_784312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_784312 prefixEnd_784312 := by exact prefixLift 784312
  have htrace : WordTrace (prefixWord ++ tailWord_784312) baseStart_784312 baseEnd_784312 := by
    simpa [prefixWord, tailWord_784312, baseEnd_784312] using wordTrace_append hprefix tailTrace_784312
  have hstable : (prefixWord ++ tailWord_784312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784312).length < 2 ^ (prefixWord ++ tailWord_784312).sum := by decide
  have hdescent : baseEnd_784312 < baseStart_784312 := by decide
  rcases family_descends (prefixWord ++ tailWord_784312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784318 : List Nat := [4, 2, 1, 1, 1, 5, 2, 1, 1, 4]
def baseStart_784318 : Nat := 118140960795 + 784318 * 2 ^ 59
def prefixEnd_784318 : Nat := 4983230072969 + 3 ^ 40 * 784318 * 2
def baseEnd_784318 : Nat := 268488079982111723945329

theorem tailTrace_784318 : CollatzResearch.WordTrace tailWord_784318 prefixEnd_784318 268488079982111723945329 := by
  unfold tailWord_784318
  simp only [CollatzResearch.WordTrace]
  refine ⟨3575803446569663961892201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19070951715038207796758405 3575803446569663961892201)
  ·
    refine ⟨2681852584927247971419151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3575803446569663961892201 2681852584927247971419151)
    ·
      refine ⟨4022778877390871957128727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2681852584927247971419151 4022778877390871957128727)
      ·
        refine ⟨6034168316086307935693091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4022778877390871957128727 6034168316086307935693091)
        ·
          refine ⟨9051252474129461903539637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6034168316086307935693091 9051252474129461903539637)
          ·
            refine ⟨848554919449637053456841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9051252474129461903539637 848554919449637053456841)
            ·
              refine ⟨636416189587227790092631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 848554919449637053456841 636416189587227790092631)
              ·
                refine ⟨954624284380841685138947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 636416189587227790092631 954624284380841685138947)
                ·
                  refine ⟨1431936426571262527708421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 954624284380841685138947 1431936426571262527708421)
                  ·
                    refine ⟨268488079982111723945329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1431936426571262527708421 268488079982111723945329)
                    ·
                      rfl

theorem cell22_784318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_784318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_784318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_784318 prefixEnd_784318 := by exact prefixLift 784318
  have htrace : WordTrace (prefixWord ++ tailWord_784318) baseStart_784318 baseEnd_784318 := by
    simpa [prefixWord, tailWord_784318, baseEnd_784318] using wordTrace_append hprefix tailTrace_784318
  have hstable : (prefixWord ++ tailWord_784318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784318).length < 2 ^ (prefixWord ++ tailWord_784318).sum := by decide
  have hdescent : baseEnd_784318 < baseStart_784318 := by decide
  rcases family_descends (prefixWord ++ tailWord_784318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784387 : List Nat := [1, 1, 1, 3, 2, 1, 1, 3, 4, 5]
def baseStart_784387 : Nat := 118140960795 + 784387 * 2 ^ 59
def prefixEnd_784387 : Nat := 4983230072969 + 3 ^ 40 * 784387 * 2
def baseEnd_784387 : Nat := 268511700092218543970117

theorem tailTrace_784387 : CollatzResearch.WordTrace tailWord_784387 prefixEnd_784387 268511700092218543970117 := by
  unfold tailWord_784387
  simp only [CollatzResearch.WordTrace]
  refine ⟨28608944209307336479399415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19072629472871557652932943 28608944209307336479399415)
  ·
    refine ⟨42913416313961004719099123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28608944209307336479399415 42913416313961004719099123)
    ·
      refine ⟨64370124470941507078648685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42913416313961004719099123 64370124470941507078648685)
      ·
        refine ⟨24138796676603065154493257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64370124470941507078648685 24138796676603065154493257)
        ·
          refine ⟨18104097507452298865869943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24138796676603065154493257 18104097507452298865869943)
          ·
            refine ⟨27156146261178448298804915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18104097507452298865869943 27156146261178448298804915)
            ·
              refine ⟨40734219391767672448207373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27156146261178448298804915 40734219391767672448207373)
              ·
                refine ⟨15275332271912877168077765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40734219391767672448207373 15275332271912877168077765)
                ·
                  refine ⟨2864124800983664469014581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15275332271912877168077765 2864124800983664469014581)
                  ·
                    refine ⟨268511700092218543970117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2864124800983664469014581 268511700092218543970117)
                    ·
                      rfl

theorem cell22_784387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 5].length) (baseStart_784387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_784387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_784387 prefixEnd_784387 := by exact prefixLift 784387
  have htrace : WordTrace (prefixWord ++ tailWord_784387) baseStart_784387 baseEnd_784387 := by
    simpa [prefixWord, tailWord_784387, baseEnd_784387] using wordTrace_append hprefix tailTrace_784387
  have hstable : (prefixWord ++ tailWord_784387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784387).length < 2 ^ (prefixWord ++ tailWord_784387).sum := by decide
  have hdescent : baseEnd_784387 < baseStart_784387 := by decide
  rcases family_descends (prefixWord ++ tailWord_784387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784419 : List Nat := [1, 1, 1, 4, 3, 1, 3, 1, 3, 4]
def baseStart_784419 : Nat := 118140960795 + 784419 * 2 ^ 59
def prefixEnd_784419 : Nat := 4983230072969 + 3 ^ 40 * 784419 * 2
def baseEnd_784419 : Nat := 268522654346181127170019

theorem tailTrace_784419 : CollatzResearch.WordTrace tailWord_784419 prefixEnd_784419 268522654346181127170019 := by
  unfold tailWord_784419
  simp only [CollatzResearch.WordTrace]
  refine ⟨28610111345191405944564311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19073407563460937296376207 28610111345191405944564311)
  ·
    refine ⟨42915167017787108916846467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28610111345191405944564311 42915167017787108916846467)
    ·
      refine ⟨64372750526680663375269701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42915167017787108916846467 64372750526680663375269701)
      ·
        refine ⟨12069890723752624382863069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64372750526680663375269701 12069890723752624382863069)
        ·
          refine ⟨4526209021407234143573651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12069890723752624382863069 4526209021407234143573651)
          ·
            refine ⟨6789313532110851215360477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4526209021407234143573651 6789313532110851215360477)
            ·
              refine ⟨2545992574541569205760179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6789313532110851215360477 2545992574541569205760179)
              ·
                refine ⟨3818988861812353808640269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2545992574541569205760179 3818988861812353808640269)
                ·
                  refine ⟨1432120823179632678240101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3818988861812353808640269 1432120823179632678240101)
                  ·
                    refine ⟨268522654346181127170019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1432120823179632678240101 268522654346181127170019)
                    ·
                      rfl

theorem cell22_784419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 3, 4].length) (baseStart_784419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_784419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_784419 prefixEnd_784419 := by exact prefixLift 784419
  have htrace : WordTrace (prefixWord ++ tailWord_784419) baseStart_784419 baseEnd_784419 := by
    simpa [prefixWord, tailWord_784419, baseEnd_784419] using wordTrace_append hprefix tailTrace_784419
  have hstable : (prefixWord ++ tailWord_784419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784419).length < 2 ^ (prefixWord ++ tailWord_784419).sum := by decide
  have hdescent : baseEnd_784419 < baseStart_784419 := by decide
  rcases family_descends (prefixWord ++ tailWord_784419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784545 : List Nat := [1, 2, 3, 3, 1, 2, 3, 3, 1, 3]
def baseStart_784545 : Nat := 118140960795 + 784545 * 2 ^ 59
def prefixEnd_784545 : Nat := 4983230072969 + 3 ^ 40 * 784545 * 2
def baseEnd_784545 : Nat := 268565786721158798519633

theorem tailTrace_784545 : CollatzResearch.WordTrace tailWord_784545 prefixEnd_784545 268565786721158798519633 := by
  unfold tailWord_784545
  simp only [CollatzResearch.WordTrace]
  refine ⟨28614706942734929463651089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19076471295156619642434059 28614706942734929463651089)
  ·
    refine ⟨21461030207051197097738317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28614706942734929463651089 21461030207051197097738317)
    ·
      refine ⟨8047886327644198911651869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21461030207051197097738317 8047886327644198911651869)
      ·
        refine ⟨3017957372866574591869451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8047886327644198911651869 3017957372866574591869451)
        ·
          refine ⟨4526936059299861887804177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3017957372866574591869451 4526936059299861887804177)
          ·
            refine ⟨3395202044474896415853133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4526936059299861887804177 3395202044474896415853133)
            ·
              refine ⟨1273200766678086155944925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3395202044474896415853133 1273200766678086155944925)
              ·
                refine ⟨477450287504282308479347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1273200766678086155944925 477450287504282308479347)
                ·
                  refine ⟨716175431256423462719021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 477450287504282308479347 716175431256423462719021)
                  ·
                    refine ⟨268565786721158798519633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 716175431256423462719021 268565786721158798519633)
                    ·
                      rfl

theorem cell22_784545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 3, 1, 3].length) (baseStart_784545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_784545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_784545 prefixEnd_784545 := by exact prefixLift 784545
  have htrace : WordTrace (prefixWord ++ tailWord_784545) baseStart_784545 baseEnd_784545 := by
    simpa [prefixWord, tailWord_784545, baseEnd_784545] using wordTrace_append hprefix tailTrace_784545
  have hstable : (prefixWord ++ tailWord_784545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784545).length < 2 ^ (prefixWord ++ tailWord_784545).sum := by decide
  have hdescent : baseEnd_784545 < baseStart_784545 := by decide
  rcases family_descends (prefixWord ++ tailWord_784545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784601 : List Nat := [1, 2, 1, 2, 3, 1, 2, 1, 6, 3]
def baseStart_784601 : Nat := 118140960795 + 784601 * 2 ^ 59
def prefixEnd_784601 : Nat := 4983230072969 + 3 ^ 40 * 784601 * 2
def baseEnd_784601 : Nat := 268584956665593319119461

theorem tailTrace_784601 : CollatzResearch.WordTrace tailWord_784601 prefixEnd_784601 268584956665593319119461 := by
  unfold tailWord_784601
  simp only [CollatzResearch.WordTrace]
  refine ⟨28616749430532051027689657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19077832953688034018459771 28616749430532051027689657)
  ·
    refine ⟨21462562072899038270767243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28616749430532051027689657 21462562072899038270767243)
    ·
      refine ⟨32193843109348557406150865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21462562072899038270767243 32193843109348557406150865)
      ·
        refine ⟨24145382332011418054613149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32193843109348557406150865 24145382332011418054613149)
        ·
          refine ⟨9054518374504281770479931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24145382332011418054613149 9054518374504281770479931)
          ·
            refine ⟨13581777561756422655719897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9054518374504281770479931 13581777561756422655719897)
            ·
              refine ⟨10186333171317316991789923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13581777561756422655719897 10186333171317316991789923)
              ·
                refine ⟨15279499756975975487684885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10186333171317316991789923 15279499756975975487684885)
                ·
                  refine ⟨716226551108248850985229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 15279499756975975487684885 716226551108248850985229)
                  ·
                    refine ⟨268584956665593319119461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 716226551108248850985229 268584956665593319119461)
                    ·
                      rfl

theorem cell22_784601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 6, 3].length) (baseStart_784601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_784601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_784601 prefixEnd_784601 := by exact prefixLift 784601
  have htrace : WordTrace (prefixWord ++ tailWord_784601) baseStart_784601 baseEnd_784601 := by
    simpa [prefixWord, tailWord_784601, baseEnd_784601] using wordTrace_append hprefix tailTrace_784601
  have hstable : (prefixWord ++ tailWord_784601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784601).length < 2 ^ (prefixWord ++ tailWord_784601).sum := by decide
  have hdescent : baseEnd_784601 < baseStart_784601 := by decide
  rcases family_descends (prefixWord ++ tailWord_784601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784648 : List Nat := [2, 1, 3, 2, 3, 2, 3, 6]
def baseStart_784648 : Nat := 118140960795 + 784648 * 2 ^ 59
def prefixEnd_784648 : Nat := 4983230072969 + 3 ^ 40 * 784648 * 2
def baseEnd_784648 : Nat := 29844560636233429243813

theorem tailTrace_784648 : CollatzResearch.WordTrace tailWord_784648 prefixEnd_784648 29844560636233429243813 := by
  unfold tailWord_784648
  simp only [CollatzResearch.WordTrace]
  refine ⟨14309231830680889027325299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19078975774241185369767065 14309231830680889027325299)
  ·
    refine ⟨21463847746021333540987949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14309231830680889027325299 21463847746021333540987949)
    ·
      refine ⟨8048942904758000077870481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21463847746021333540987949 8048942904758000077870481)
      ·
        refine ⟨6036707178568500058402861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8048942904758000077870481 6036707178568500058402861)
        ·
          refine ⟨2263765191963187521901073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6036707178568500058402861 2263765191963187521901073)
          ·
            refine ⟨1697823893972390641425805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2263765191963187521901073 1697823893972390641425805)
            ·
              refine ⟨636683960239646490534677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1697823893972390641425805 636683960239646490534677)
              ·
                refine ⟨29844560636233429243813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 636683960239646490534677 29844560636233429243813)
                ·
                  rfl

theorem cell22_784648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 6].length) (baseStart_784648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_784648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_784648 prefixEnd_784648 := by exact prefixLift 784648
  have htrace : WordTrace (prefixWord ++ tailWord_784648) baseStart_784648 baseEnd_784648 := by
    simpa [prefixWord, tailWord_784648, baseEnd_784648] using wordTrace_append hprefix tailTrace_784648
  have hstable : (prefixWord ++ tailWord_784648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784648).length < 2 ^ (prefixWord ++ tailWord_784648).sum := by decide
  have hdescent : baseEnd_784648 < baseStart_784648 := by decide
  rcases family_descends (prefixWord ++ tailWord_784648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784669 : List Nat := [1, 4, 2, 3, 3, 1, 1, 2, 2, 3]
def baseStart_784669 : Nat := 118140960795 + 784669 * 2 ^ 59
def prefixEnd_784669 : Nat := 4983230072969 + 3 ^ 40 * 784669 * 2
def baseEnd_784669 : Nat := 268608234455263808419253

theorem tailTrace_784669 : CollatzResearch.WordTrace tailWord_784669 prefixEnd_784669 268608234455263808419253 := by
  unfold tailWord_784669
  simp only [CollatzResearch.WordTrace]
  refine ⟨28619229594285698641165061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19079486396190465760776707 28619229594285698641165061)
  ·
    refine ⟨5366105548928568495218449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28619229594285698641165061 5366105548928568495218449)
    ·
      refine ⟨4024579161696426371413837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5366105548928568495218449 4024579161696426371413837)
      ·
        refine ⟨1509217185636159889280189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4024579161696426371413837 1509217185636159889280189)
        ·
          refine ⟨565956444613559958480071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1509217185636159889280189 565956444613559958480071)
          ·
            refine ⟨848934666920339937720107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 565956444613559958480071 848934666920339937720107)
            ·
              refine ⟨1273402000380509906580161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 848934666920339937720107 1273402000380509906580161)
              ·
                refine ⟨955051500285382429935121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1273402000380509906580161 955051500285382429935121)
                ·
                  refine ⟨716288625214036822451341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 955051500285382429935121 716288625214036822451341)
                  ·
                    refine ⟨268608234455263808419253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 716288625214036822451341 268608234455263808419253)
                    ·
                      rfl

theorem cell22_784669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_784669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_784669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_784669 prefixEnd_784669 := by exact prefixLift 784669
  have htrace : WordTrace (prefixWord ++ tailWord_784669) baseStart_784669 baseEnd_784669 := by
    simpa [prefixWord, tailWord_784669, baseEnd_784669] using wordTrace_append hprefix tailTrace_784669
  have hstable : (prefixWord ++ tailWord_784669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784669).length < 2 ^ (prefixWord ++ tailWord_784669).sum := by decide
  have hdescent : baseEnd_784669 < baseStart_784669 := by decide
  rcases family_descends (prefixWord ++ tailWord_784669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784691 : List Nat := [1, 1, 1, 2, 5, 1, 1, 3, 2, 5]
def baseStart_784691 : Nat := 118140960795 + 784691 * 2 ^ 59
def prefixEnd_784691 : Nat := 4983230072969 + 3 ^ 40 * 784691 * 2
def baseEnd_784691 : Nat := 268615765504863084369185

theorem tailTrace_784691 : CollatzResearch.WordTrace tailWord_784691 prefixEnd_784691 268615765504863084369185 := by
  unfold tailWord_784691
  simp only [CollatzResearch.WordTrace]
  refine ⟨28620032000205996398465927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19080021333470664265643951 28620032000205996398465927)
  ·
    refine ⟨42930048000308994597698891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28620032000205996398465927 42930048000308994597698891)
    ·
      refine ⟨64395072000463491896548337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42930048000308994597698891 64395072000463491896548337)
      ·
        refine ⟨48296304000347618922411253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64395072000463491896548337 48296304000347618922411253)
        ·
          refine ⟨4527778500032589273976055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48296304000347618922411253 4527778500032589273976055)
          ·
            refine ⟨6791667750048883910964083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4527778500032589273976055 6791667750048883910964083)
            ·
              refine ⟨10187501625073325866446125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6791667750048883910964083 10187501625073325866446125)
              ·
                refine ⟨3820313109402497199917297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10187501625073325866446125 3820313109402497199917297)
                ·
                  refine ⟨2865234832051872899937973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3820313109402497199917297 2865234832051872899937973)
                  ·
                    refine ⟨268615765504863084369185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2865234832051872899937973 268615765504863084369185)
                    ·
                      rfl

theorem cell22_784691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 5].length) (baseStart_784691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_784691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_784691 prefixEnd_784691 := by exact prefixLift 784691
  have htrace : WordTrace (prefixWord ++ tailWord_784691) baseStart_784691 baseEnd_784691 := by
    simpa [prefixWord, tailWord_784691, baseEnd_784691] using wordTrace_append hprefix tailTrace_784691
  have hstable : (prefixWord ++ tailWord_784691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784691).length < 2 ^ (prefixWord ++ tailWord_784691).sum := by decide
  have hdescent : baseEnd_784691 < baseStart_784691 := by decide
  rcases family_descends (prefixWord ++ tailWord_784691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784751 : List Nat := [1, 1, 2, 1, 3, 1, 2, 4, 1, 6]
def baseStart_784751 : Nat := 118140960795 + 784751 * 2 ^ 59
def prefixEnd_784751 : Nat := 4983230072969 + 3 ^ 40 * 784751 * 2
def baseEnd_784751 : Nat := 268636304731042927869001

theorem tailTrace_784751 : CollatzResearch.WordTrace tailWord_784751 prefixEnd_784751 268636304731042927869001 := by
  unfold tailWord_784751
  simp only [CollatzResearch.WordTrace]
  refine ⟨28622220379988626645650107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19081480253325751097100071 28622220379988626645650107)
  ·
    refine ⟨42933330569982939968475161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28622220379988626645650107 42933330569982939968475161)
    ·
      refine ⟨32199997927487204976356371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42933330569982939968475161 32199997927487204976356371)
      ·
        refine ⟨48299996891230807464534557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32199997927487204976356371 48299996891230807464534557)
        ·
          refine ⟨18112498834211552799200459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48299996891230807464534557 18112498834211552799200459)
          ·
            refine ⟨27168748251317329198800689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18112498834211552799200459 27168748251317329198800689)
            ·
              refine ⟨20376561188487996899100517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27168748251317329198800689 20376561188487996899100517)
              ·
                refine ⟨3820605222841499418581347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20376561188487996899100517 3820605222841499418581347)
                ·
                  refine ⟨5730907834262249127872021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3820605222841499418581347 5730907834262249127872021)
                  ·
                    refine ⟨268636304731042927869001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5730907834262249127872021 268636304731042927869001)
                    ·
                      rfl

theorem cell22_784751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 6].length) (baseStart_784751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_784751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_784751 prefixEnd_784751 := by exact prefixLift 784751
  have htrace : WordTrace (prefixWord ++ tailWord_784751) baseStart_784751 baseEnd_784751 := by
    simpa [prefixWord, tailWord_784751, baseEnd_784751] using wordTrace_append hprefix tailTrace_784751
  have hstable : (prefixWord ++ tailWord_784751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784751).length < 2 ^ (prefixWord ++ tailWord_784751).sum := by decide
  have hdescent : baseEnd_784751 < baseStart_784751 := by decide
  rcases family_descends (prefixWord ++ tailWord_784751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784757 : List Nat := [1, 3, 4, 1, 2, 3, 1, 2, 1, 4]
def baseStart_784757 : Nat := 118140960795 + 784757 * 2 ^ 59
def prefixEnd_784757 : Nat := 4983230072969 + 3 ^ 40 * 784757 * 2
def baseEnd_784757 : Nat := 268638358653660912218983

theorem tailTrace_784757 : CollatzResearch.WordTrace tailWord_784757 prefixEnd_784757 268638358653660912218983 := by
  unfold tailWord_784757
  simp only [CollatzResearch.WordTrace]
  refine ⟨28622439217966889670368525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19081626145311259780245683 28622439217966889670368525)
  ·
    refine ⟨10733414706737583626388197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28622439217966889670368525 10733414706737583626388197)
    ·
      refine ⟨2012515257513296929947787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10733414706737583626388197 2012515257513296929947787)
      ·
        refine ⟨3018772886269945394921681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2012515257513296929947787 3018772886269945394921681)
        ·
          refine ⟨2264079664702459046191261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3018772886269945394921681 2264079664702459046191261)
          ·
            refine ⟨849029874263422142321723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2264079664702459046191261 849029874263422142321723)
            ·
              refine ⟨1273544811395133213482585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 849029874263422142321723 1273544811395133213482585)
              ·
                refine ⟨955158608546349910111939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1273544811395133213482585 955158608546349910111939)
                ·
                  refine ⟨1432737912819524865167909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 955158608546349910111939 1432737912819524865167909)
                  ·
                    refine ⟨268638358653660912218983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1432737912819524865167909 268638358653660912218983)
                    ·
                      rfl

theorem cell22_784757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_784757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_784757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_784757 prefixEnd_784757 := by exact prefixLift 784757
  have htrace : WordTrace (prefixWord ++ tailWord_784757) baseStart_784757 baseEnd_784757 := by
    simpa [prefixWord, tailWord_784757, baseEnd_784757] using wordTrace_append hprefix tailTrace_784757
  have hstable : (prefixWord ++ tailWord_784757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784757).length < 2 ^ (prefixWord ++ tailWord_784757).sum := by decide
  have hdescent : baseEnd_784757 < baseStart_784757 := by decide
  rcases family_descends (prefixWord ++ tailWord_784757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784875 : List Nat := [1, 1, 1, 1, 2, 3, 6, 2, 1, 4]
def baseStart_784875 : Nat := 118140960795 + 784875 * 2 ^ 59
def prefixEnd_784875 : Nat := 4983230072969 + 3 ^ 40 * 784875 * 2
def baseEnd_784875 : Nat := 268678752465147937768621

theorem tailTrace_784875 : CollatzResearch.WordTrace tailWord_784875 prefixEnd_784875 268678752465147937768621 := by
  unfold tailWord_784875
  simp only [CollatzResearch.WordTrace]
  refine ⟨28626743031539395823164079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19084495354359597215442719 28626743031539395823164079)
  ·
    refine ⟨42940114547309093734746119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28626743031539395823164079 42940114547309093734746119)
    ·
      refine ⟨64410171820963640602119179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42940114547309093734746119 64410171820963640602119179)
      ·
        refine ⟨96615257731445460903178769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64410171820963640602119179 96615257731445460903178769)
        ·
          refine ⟨72461443298584095677384077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96615257731445460903178769 72461443298584095677384077)
          ·
            refine ⟨27173041236969035879019029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72461443298584095677384077 27173041236969035879019029)
            ·
              refine ⟨1273736307982923556829017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27173041236969035879019029 1273736307982923556829017)
              ·
                refine ⟨955302230987192667621763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1273736307982923556829017 955302230987192667621763)
                ·
                  refine ⟨1432953346480789001432645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 955302230987192667621763 1432953346480789001432645)
                  ·
                    refine ⟨268678752465147937768621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1432953346480789001432645 268678752465147937768621)
                    ·
                      rfl

theorem cell22_784875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 2, 1, 4].length) (baseStart_784875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_784875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_784875 prefixEnd_784875 := by exact prefixLift 784875
  have htrace : WordTrace (prefixWord ++ tailWord_784875) baseStart_784875 baseEnd_784875 := by
    simpa [prefixWord, tailWord_784875, baseEnd_784875] using wordTrace_append hprefix tailTrace_784875
  have hstable : (prefixWord ++ tailWord_784875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784875).length < 2 ^ (prefixWord ++ tailWord_784875).sum := by decide
  have hdescent : baseEnd_784875 < baseStart_784875 := by decide
  rcases family_descends (prefixWord ++ tailWord_784875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784888 : List Nat := [2, 1, 2, 1, 1, 4, 2, 1, 3, 5]
def baseStart_784888 : Nat := 118140960795 + 784888 * 2 ^ 59
def prefixEnd_784888 : Nat := 4983230072969 + 3 ^ 40 * 784888 * 2
def baseEnd_784888 : Nat := 268683202630820237193581

theorem tailTrace_784888 : CollatzResearch.WordTrace tailWord_784888 prefixEnd_784888 268683202630820237193581 := by
  unfold tailWord_784888
  simp only [CollatzResearch.WordTrace]
  refine ⟨14313608590246149521693659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19084811453661532695591545 14313608590246149521693659)
  ·
    refine ⟨21470412885369224282540489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14313608590246149521693659 21470412885369224282540489)
    ·
      refine ⟨16102809664026918211905367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21470412885369224282540489 16102809664026918211905367)
      ·
        refine ⟨24154214496040377317858051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16102809664026918211905367 24154214496040377317858051)
        ·
          refine ⟨36231321744060565976787077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24154214496040377317858051 36231321744060565976787077)
          ·
            refine ⟨6793372827011356120647577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36231321744060565976787077 6793372827011356120647577)
            ·
              refine ⟨5095029620258517090485683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6793372827011356120647577 5095029620258517090485683)
              ·
                refine ⟨7642544430387775635728525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5095029620258517090485683 7642544430387775635728525)
                ·
                  refine ⟨2865954161395415863398197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7642544430387775635728525 2865954161395415863398197)
                  ·
                    refine ⟨268683202630820237193581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2865954161395415863398197 268683202630820237193581)
                    ·
                      rfl

theorem cell22_784888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 3, 5].length) (baseStart_784888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_784888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_784888 prefixEnd_784888 := by exact prefixLift 784888
  have htrace : WordTrace (prefixWord ++ tailWord_784888) baseStart_784888 baseEnd_784888 := by
    simpa [prefixWord, tailWord_784888, baseEnd_784888] using wordTrace_append hprefix tailTrace_784888
  have hstable : (prefixWord ++ tailWord_784888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784888).length < 2 ^ (prefixWord ++ tailWord_784888).sum := by decide
  have hdescent : baseEnd_784888 < baseStart_784888 := by decide
  rcases family_descends (prefixWord ++ tailWord_784888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784890 : List Nat := [3, 1, 1, 1, 1, 2, 2, 7, 4]
def baseStart_784890 : Nat := 118140960795 + 784890 * 2 ^ 59
def prefixEnd_784890 : Nat := 4983230072969 + 3 ^ 40 * 784890 * 2
def baseEnd_784890 : Nat := 89561295757230966214525

theorem tailTrace_784890 : CollatzResearch.WordTrace tailWord_784890 prefixEnd_784890 89561295757230966214525 := by
  unfold tailWord_784890
  simp only [CollatzResearch.WordTrace]
  refine ⟨7156822531621263346240031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19084860084323368923306749 7156822531621263346240031)
  ·
    refine ⟨10735233797431895019360047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7156822531621263346240031 10735233797431895019360047)
    ·
      refine ⟨16102850696147842529040071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10735233797431895019360047 16102850696147842529040071)
      ·
        refine ⟨24154276044221763793560107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16102850696147842529040071 24154276044221763793560107)
        ·
          refine ⟨36231414066332645690340161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24154276044221763793560107 36231414066332645690340161)
          ·
            refine ⟨27173560549749484267755121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36231414066332645690340161 27173560549749484267755121)
            ·
              refine ⟨20380170412312113200816341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27173560549749484267755121 20380170412312113200816341)
              ·
                refine ⟨477660244038565153144133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 20380170412312113200816341 477660244038565153144133)
                ·
                  refine ⟨89561295757230966214525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 477660244038565153144133 89561295757230966214525)
                  ·
                    rfl

theorem cell22_784890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 7, 4].length) (baseStart_784890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_784890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_784890 prefixEnd_784890 := by exact prefixLift 784890
  have htrace : WordTrace (prefixWord ++ tailWord_784890) baseStart_784890 baseEnd_784890 := by
    simpa [prefixWord, tailWord_784890, baseEnd_784890] using wordTrace_append hprefix tailTrace_784890
  have hstable : (prefixWord ++ tailWord_784890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784890).length < 2 ^ (prefixWord ++ tailWord_784890).sum := by decide
  have hdescent : baseEnd_784890 < baseStart_784890 := by decide
  rcases family_descends (prefixWord ++ tailWord_784890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784933 : List Nat := [1, 3, 1, 2, 2, 1, 2, 1, 2, 7]
def baseStart_784933 : Nat := 118140960795 + 784933 * 2 ^ 59
def prefixEnd_784933 : Nat := 4983230072969 + 3 ^ 40 * 784933 * 2
def baseEnd_784933 : Nat := 268698607050455119818443

theorem tailTrace_784933 : CollatzResearch.WordTrace tailWord_784933 prefixEnd_784933 268698607050455119818443 := by
  unfold tailWord_784933
  simp only [CollatzResearch.WordTrace]
  refine ⟨28628858465329271728775453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19085905643552847819183635 28628858465329271728775453)
  ·
    refine ⟨10735821924498476898290795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28628858465329271728775453 10735821924498476898290795)
    ·
      refine ⟨16103732886747715347436193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10735821924498476898290795 16103732886747715347436193)
      ·
        refine ⟨12077799665060786510577145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16103732886747715347436193 12077799665060786510577145)
        ·
          refine ⟨9058349748795589882932859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12077799665060786510577145 9058349748795589882932859)
          ·
            refine ⟨13587524623193384824399289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9058349748795589882932859 13587524623193384824399289)
            ·
              refine ⟨10190643467395038618299467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13587524623193384824399289 10190643467395038618299467)
              ·
                refine ⟨15285965201092557927449201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10190643467395038618299467 15285965201092557927449201)
                ·
                  refine ⟨11464473900819418445586901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15285965201092557927449201 11464473900819418445586901)
                  ·
                    refine ⟨268698607050455119818443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11464473900819418445586901 268698607050455119818443)
                    ·
                      rfl

theorem cell22_784933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 7].length) (baseStart_784933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_784933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_784933 prefixEnd_784933 := by exact prefixLift 784933
  have htrace : WordTrace (prefixWord ++ tailWord_784933) baseStart_784933 baseEnd_784933 := by
    simpa [prefixWord, tailWord_784933, baseEnd_784933] using wordTrace_append hprefix tailTrace_784933
  have hstable : (prefixWord ++ tailWord_784933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784933).length < 2 ^ (prefixWord ++ tailWord_784933).sum := by decide
  have hdescent : baseEnd_784933 < baseStart_784933 := by decide
  rcases family_descends (prefixWord ++ tailWord_784933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784958 : List Nat := [4, 2, 1, 4, 1, 2, 2, 2, 4]
def baseStart_784958 : Nat := 118140960795 + 784958 * 2 ^ 59
def prefixEnd_784958 : Nat := 4983230072969 + 3 ^ 40 * 784958 * 2
def baseEnd_784958 : Nat := 89569055020454462647789

theorem tailTrace_784958 : CollatzResearch.WordTrace tailWord_784958 prefixEnd_784958 89569055020454462647789 := by
  unfold tailWord_784958
  simp only [CollatzResearch.WordTrace]
  refine ⟨3578721286279837624804441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19086513526825800665623685 3578721286279837624804441)
  ·
    refine ⟨2684040964709878218603331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3578721286279837624804441 2684040964709878218603331)
    ·
      refine ⟨4026061447064817327904997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2684040964709878218603331 4026061447064817327904997)
      ·
        refine ⟨754886521324653248982187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4026061447064817327904997 754886521324653248982187)
        ·
          refine ⟨1132329781986979873473281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 754886521324653248982187 1132329781986979873473281)
          ·
            refine ⟨849247336490234905104961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1132329781986979873473281 849247336490234905104961)
            ·
              refine ⟨636935502367676178828721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 849247336490234905104961 636935502367676178828721)
              ·
                refine ⟨477701626775757134121541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 636935502367676178828721 477701626775757134121541)
                ·
                  refine ⟨89569055020454462647789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 477701626775757134121541 89569055020454462647789)
                  ·
                    rfl

theorem cell22_784958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_784958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_784958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_784958 prefixEnd_784958 := by exact prefixLift 784958
  have htrace : WordTrace (prefixWord ++ tailWord_784958) baseStart_784958 baseEnd_784958 := by
    simpa [prefixWord, tailWord_784958, baseEnd_784958] using wordTrace_append hprefix tailTrace_784958
  have hstable : (prefixWord ++ tailWord_784958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784958).length < 2 ^ (prefixWord ++ tailWord_784958).sum := by decide
  have hdescent : baseEnd_784958 < baseStart_784958 := by decide
  rcases family_descends (prefixWord ++ tailWord_784958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784963 : List Nat := [1, 1, 1, 3, 1, 2, 1, 5, 7]
def baseStart_784963 : Nat := 118140960795 + 784963 * 2 ^ 59
def prefixEnd_784963 : Nat := 4983230072969 + 3 ^ 40 * 784963 * 2
def baseEnd_784963 : Nat := 89569625554515013856117

theorem tailTrace_784963 : CollatzResearch.WordTrace tailWord_784963 prefixEnd_784963 89569625554515013856117 := by
  unfold tailWord_784963
  simp only [CollatzResearch.WordTrace]
  refine ⟨28629952655220586852367543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19086635103480391234911695 28629952655220586852367543)
  ·
    refine ⟨42944928982830880278551315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28629952655220586852367543 42944928982830880278551315)
    ·
      refine ⟨64417393474246320417826973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42944928982830880278551315 64417393474246320417826973)
      ·
        refine ⟨24156522552842370156685115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64417393474246320417826973 24156522552842370156685115)
        ·
          refine ⟨36234783829263555235027673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24156522552842370156685115 36234783829263555235027673)
          ·
            refine ⟨27176087871947666426270755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36234783829263555235027673 27176087871947666426270755)
            ·
              refine ⟨40764131807921499639406133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27176087871947666426270755 40764131807921499639406133)
              ·
                refine ⟨3821637356992640591194325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40764131807921499639406133 3821637356992640591194325)
                ·
                  refine ⟨89569625554515013856117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3821637356992640591194325 89569625554515013856117)
                  ·
                    rfl

theorem cell22_784963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 7].length) (baseStart_784963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_784963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_784963 prefixEnd_784963 := by exact prefixLift 784963
  have htrace : WordTrace (prefixWord ++ tailWord_784963) baseStart_784963 baseEnd_784963 := by
    simpa [prefixWord, tailWord_784963, baseEnd_784963] using wordTrace_append hprefix tailTrace_784963
  have hstable : (prefixWord ++ tailWord_784963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784963).length < 2 ^ (prefixWord ++ tailWord_784963).sum := by decide
  have hdescent : baseEnd_784963 < baseStart_784963 := by decide
  rcases family_descends (prefixWord ++ tailWord_784963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785042 : List Nat := [3, 2, 3, 1, 2, 1, 2, 2, 6]
def baseStart_785042 : Nat := 118140960795 + 785042 * 2 ^ 59
def prefixEnd_785042 : Nat := 4983230072969 + 3 ^ 40 * 785042 * 2
def baseEnd_785042 : Nat := 89578639992671722947703

theorem tailTrace_785042 : CollatzResearch.WordTrace tailWord_785042 prefixEnd_785042 89578639992671722947703 := by
  unfold tailWord_785042
  simp only [CollatzResearch.WordTrace]
  refine ⟨7158208505483595836123345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19088556014622922229662253 7158208505483595836123345)
  ·
    refine ⟨5368656379112696877092509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7158208505483595836123345 5368656379112696877092509)
    ·
      refine ⟨2013246142167261328909691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5368656379112696877092509 2013246142167261328909691)
      ·
        refine ⟨3019869213250891993364537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2013246142167261328909691 3019869213250891993364537)
        ·
          refine ⟨2264901909938168995023403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3019869213250891993364537 2264901909938168995023403)
          ·
            refine ⟨3397352864907253492535105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2264901909938168995023403 3397352864907253492535105)
            ·
              refine ⟨2548014648680440119401329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3397352864907253492535105 2548014648680440119401329)
              ·
                refine ⟨1911010986510330089550997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2548014648680440119401329 1911010986510330089550997)
                ·
                  refine ⟨89578639992671722947703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1911010986510330089550997 89578639992671722947703)
                  ·
                    rfl

theorem cell22_785042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 6].length) (baseStart_785042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_785042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_785042 prefixEnd_785042 := by exact prefixLift 785042
  have htrace : WordTrace (prefixWord ++ tailWord_785042) baseStart_785042 baseEnd_785042 := by
    simpa [prefixWord, tailWord_785042, baseEnd_785042] using wordTrace_append hprefix tailTrace_785042
  have hstable : (prefixWord ++ tailWord_785042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785042).length < 2 ^ (prefixWord ++ tailWord_785042).sum := by decide
  have hdescent : baseEnd_785042 < baseStart_785042 := by decide
  rcases family_descends (prefixWord ++ tailWord_785042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785044 : List Nat := [2, 4, 2, 2, 1, 1, 1, 4, 1, 4]
def baseStart_785044 : Nat := 118140960795 + 785044 * 2 ^ 59
def prefixEnd_785044 : Nat := 4983230072969 + 3 ^ 40 * 785044 * 2
def baseEnd_785044 : Nat := 268736604618887830293103

theorem tailTrace_785044 : CollatzResearch.WordTrace tailWord_785044 prefixEnd_785044 268736604618887830293103 := by
  unfold tailWord_785044
  simp only [CollatzResearch.WordTrace]
  refine ⟨14316453483963568843033093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19088604645284758457377457 14316453483963568843033093)
  ·
    refine ⟨2684335028243169158068705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14316453483963568843033093 2684335028243169158068705)
    ·
      refine ⟨2013251271182376868551529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2684335028243169158068705 2013251271182376868551529)
      ·
        refine ⟨1509938453386782651413647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2013251271182376868551529 1509938453386782651413647)
        ·
          refine ⟨2264907680080173977120471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1509938453386782651413647 2264907680080173977120471)
          ·
            refine ⟨3397361520120260965680707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2264907680080173977120471 3397361520120260965680707)
            ·
              refine ⟨5096042280180391448521061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3397361520120260965680707 5096042280180391448521061)
              ·
                refine ⟨955507927533823396597699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5096042280180391448521061 955507927533823396597699)
                ·
                  refine ⟨1433261891300735094896549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 955507927533823396597699 1433261891300735094896549)
                  ·
                    refine ⟨268736604618887830293103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1433261891300735094896549 268736604618887830293103)
                    ·
                      rfl

theorem cell22_785044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_785044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_785044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_785044 prefixEnd_785044 := by exact prefixLift 785044
  have htrace : WordTrace (prefixWord ++ tailWord_785044) baseStart_785044 baseEnd_785044 := by
    simpa [prefixWord, tailWord_785044, baseEnd_785044] using wordTrace_append hprefix tailTrace_785044
  have hstable : (prefixWord ++ tailWord_785044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785044).length < 2 ^ (prefixWord ++ tailWord_785044).sum := by decide
  have hdescent : baseEnd_785044 < baseStart_785044 := by decide
  rcases family_descends (prefixWord ++ tailWord_785044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785162 : List Nat := [3, 1, 2, 2, 1, 2, 1, 3, 3, 4]
def baseStart_785162 : Nat := 118140960795 + 785162 * 2 ^ 59
def prefixEnd_785162 : Nat := 4983230072969 + 3 ^ 40 * 785162 * 2
def baseEnd_785162 : Nat := 268776998430374855842741

theorem tailTrace_785162 : CollatzResearch.WordTrace tailWord_785162 prefixEnd_785162 268776998430374855842741 := by
  unfold tailWord_785162
  simp only [CollatzResearch.WordTrace]
  refine ⟨7159302695374910959715435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19091473854333095892574493 7159302695374910959715435)
  ·
    refine ⟨10738954043062366439573153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7159302695374910959715435 10738954043062366439573153)
    ·
      refine ⟨8054215532296774829679865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10738954043062366439573153 8054215532296774829679865)
      ·
        refine ⟨6040661649222581122259899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8054215532296774829679865 6040661649222581122259899)
        ·
          refine ⟨9060992473833871683389849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6040661649222581122259899 9060992473833871683389849)
          ·
            refine ⟨6795744355375403762542387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9060992473833871683389849 6795744355375403762542387)
            ·
              refine ⟨10193616533063105643813581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6795744355375403762542387 10193616533063105643813581)
              ·
                refine ⟨3822606199898664616430093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10193616533063105643813581 3822606199898664616430093)
                ·
                  refine ⟨1433477324961999231161285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3822606199898664616430093 1433477324961999231161285)
                  ·
                    refine ⟨268776998430374855842741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1433477324961999231161285 268776998430374855842741)
                    ·
                      rfl

theorem cell22_785162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_785162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_785162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_785162 prefixEnd_785162 := by exact prefixLift 785162
  have htrace : WordTrace (prefixWord ++ tailWord_785162) baseStart_785162 baseEnd_785162 := by
    simpa [prefixWord, tailWord_785162, baseEnd_785162] using wordTrace_append hprefix tailTrace_785162
  have hstable : (prefixWord ++ tailWord_785162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785162).length < 2 ^ (prefixWord ++ tailWord_785162).sum := by decide
  have hdescent : baseEnd_785162 < baseStart_785162 := by decide
  rcases family_descends (prefixWord ++ tailWord_785162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785170 : List Nat := [3, 2, 4, 1, 2, 1, 2, 3, 1, 3]
def baseStart_785170 : Nat := 118140960795 + 785170 * 2 ^ 59
def prefixEnd_785170 : Nat := 4983230072969 + 3 ^ 40 * 785170 * 2
def baseEnd_785170 : Nat := 268779736993865501642717

theorem tailTrace_785170 : CollatzResearch.WordTrace tailWord_785170 prefixEnd_785170 268779736993865501642717 := by
  unfold tailWord_785170
  simp only [CollatzResearch.WordTrace]
  refine ⟨7159375641367665301288241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19091668376980440803435309 7159375641367665301288241)
  ·
    refine ⟨5369531731025748975966181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7159375641367665301288241 5369531731025748975966181)
    ·
      refine ⟨1006787199567327932993659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5369531731025748975966181 1006787199567327932993659)
      ·
        refine ⟨1510180799350991899490489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1006787199567327932993659 1510180799350991899490489)
        ·
          refine ⟨1132635599513243924617867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1510180799350991899490489 1132635599513243924617867)
          ·
            refine ⟨1698953399269865886926801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1132635599513243924617867 1698953399269865886926801)
            ·
              refine ⟨1274215049452399415195101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1698953399269865886926801 1274215049452399415195101)
              ·
                refine ⟨477830643544649780698163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1274215049452399415195101 477830643544649780698163)
                ·
                  refine ⟨716745965316974671047245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 477830643544649780698163 716745965316974671047245)
                  ·
                    refine ⟨268779736993865501642717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 716745965316974671047245 268779736993865501642717)
                    ·
                      rfl

theorem cell22_785170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_785170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_785170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_785170 prefixEnd_785170 := by exact prefixLift 785170
  have htrace : WordTrace (prefixWord ++ tailWord_785170) baseStart_785170 baseEnd_785170 := by
    simpa [prefixWord, tailWord_785170, baseEnd_785170] using wordTrace_append hprefix tailTrace_785170
  have hstable : (prefixWord ++ tailWord_785170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785170).length < 2 ^ (prefixWord ++ tailWord_785170).sum := by decide
  have hdescent : baseEnd_785170 < baseStart_785170 := by decide
  rcases family_descends (prefixWord ++ tailWord_785170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785344 : List Nat := [2, 1, 1, 2, 3, 3, 2, 2, 1, 5]
def baseStart_785344 : Nat := 118140960795 + 785344 * 2 ^ 59
def prefixEnd_785344 : Nat := 4983230072969 + 3 ^ 40 * 785344 * 2
def baseEnd_785344 : Nat := 268839300749787047792183

theorem tailTrace_785344 : CollatzResearch.WordTrace tailWord_785344 prefixEnd_785344 268839300749787047792183 := by
  unfold tailWord_785344
  simp only [CollatzResearch.WordTrace]
  refine ⟨14321924433420144460993543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19095899244560192614658057 14321924433420144460993543)
  ·
    refine ⟨21482886650130216691490315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14321924433420144460993543 21482886650130216691490315)
    ·
      refine ⟨32224329975195325037235473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21482886650130216691490315 32224329975195325037235473)
      ·
        refine ⟨24168247481396493777926605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32224329975195325037235473 24168247481396493777926605)
        ·
          refine ⟨9063092805523685166722477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24168247481396493777926605 9063092805523685166722477)
          ·
            refine ⟨3398659802071381937520929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9063092805523685166722477 3398659802071381937520929)
            ·
              refine ⟨2548994851553536453140697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3398659802071381937520929 2548994851553536453140697)
              ·
                refine ⟨1911746138665152339855523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2548994851553536453140697 1911746138665152339855523)
                ·
                  refine ⟨2867619207997728509783285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1911746138665152339855523 2867619207997728509783285)
                  ·
                    refine ⟨268839300749787047792183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2867619207997728509783285 268839300749787047792183)
                    ·
                      rfl

theorem cell22_785344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 1, 5].length) (baseStart_785344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_785344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_785344 prefixEnd_785344 := by exact prefixLift 785344
  have htrace : WordTrace (prefixWord ++ tailWord_785344) baseStart_785344 baseEnd_785344 := by
    simpa [prefixWord, tailWord_785344, baseEnd_785344] using wordTrace_append hprefix tailTrace_785344
  have hstable : (prefixWord ++ tailWord_785344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785344).length < 2 ^ (prefixWord ++ tailWord_785344).sum := by decide
  have hdescent : baseEnd_785344 < baseStart_785344 := by decide
  rcases family_descends (prefixWord ++ tailWord_785344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785378 : List Nat := [3, 3, 3, 1, 1, 1, 3, 1, 1, 5]
def baseStart_785378 : Nat := 118140960795 + 785378 * 2 ^ 59
def prefixEnd_785378 : Nat := 4983230072969 + 3 ^ 40 * 785378 * 2
def baseEnd_785378 : Nat := 268850939644622292442079

theorem tailTrace_785378 : CollatzResearch.WordTrace tailWord_785378 prefixEnd_785378 268850939644622292442079 := by
  unfold tailWord_785378
  simp only [CollatzResearch.WordTrace]
  refine ⟨7161272237179278182181197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19096725965811408485816525 7161272237179278182181197)
  ·
    refine ⟨2685477088942229318317949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7161272237179278182181197 2685477088942229318317949)
    ·
      refine ⟨1007053908353335994369231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2685477088942229318317949 1007053908353335994369231)
      ·
        refine ⟨1510580862530003991553847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1007053908353335994369231 1510580862530003991553847)
        ·
          refine ⟨2265871293795005987330771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1510580862530003991553847 2265871293795005987330771)
          ·
            refine ⟨3398806940692508980996157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2265871293795005987330771 3398806940692508980996157)
            ·
              refine ⟨1274552602759690867873559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3398806940692508980996157 1274552602759690867873559)
              ·
                refine ⟨1911828904139536301810339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1274552602759690867873559 1911828904139536301810339)
                ·
                  refine ⟨2867743356209304452715509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1911828904139536301810339 2867743356209304452715509)
                  ·
                    refine ⟨268850939644622292442079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2867743356209304452715509 268850939644622292442079)
                    ·
                      rfl

theorem cell22_785378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_785378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_785378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_785378 prefixEnd_785378 := by exact prefixLift 785378
  have htrace : WordTrace (prefixWord ++ tailWord_785378) baseStart_785378 baseEnd_785378 := by
    simpa [prefixWord, tailWord_785378, baseEnd_785378] using wordTrace_append hprefix tailTrace_785378
  have hstable : (prefixWord ++ tailWord_785378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785378).length < 2 ^ (prefixWord ++ tailWord_785378).sum := by decide
  have hdescent : baseEnd_785378 < baseStart_785378 := by decide
  rcases family_descends (prefixWord ++ tailWord_785378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785391 : List Nat := [1, 1, 2, 1, 4, 5, 2, 6]
def baseStart_785391 : Nat := 118140960795 + 785391 * 2 ^ 59
def prefixEnd_785391 : Nat := 4983230072969 + 3 ^ 40 * 785391 * 2
def baseEnd_785391 : Nat := 29872821090032732429671

theorem tailTrace_785391 : CollatzResearch.WordTrace tailWord_785391 prefixEnd_785391 29872821090032732429671 := by
  unfold tailWord_785391
  simp only [CollatzResearch.WordTrace]
  refine ⟨28645563097670015948948027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19097042065113343965965351 28645563097670015948948027)
  ·
    refine ⟨42968344646505023923422041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28645563097670015948948027 42968344646505023923422041)
    ·
      refine ⟨32226258484878767942566531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42968344646505023923422041 32226258484878767942566531)
      ·
        refine ⟨48339387727318151913849797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32226258484878767942566531 48339387727318151913849797)
        ·
          refine ⟨9063635198872153483846837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48339387727318151913849797 9063635198872153483846837)
          ·
            refine ⟨849715799894264389110641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9063635198872153483846837 849715799894264389110641)
            ·
              refine ⟨637286849920698291832981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 849715799894264389110641 637286849920698291832981)
              ·
                refine ⟨29872821090032732429671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 637286849920698291832981 29872821090032732429671)
                ·
                  rfl

theorem cell22_785391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 6].length) (baseStart_785391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_785391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_785391 prefixEnd_785391 := by exact prefixLift 785391
  have htrace : WordTrace (prefixWord ++ tailWord_785391) baseStart_785391 baseEnd_785391 := by
    simpa [prefixWord, tailWord_785391, baseEnd_785391] using wordTrace_append hprefix tailTrace_785391
  have hstable : (prefixWord ++ tailWord_785391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785391).length < 2 ^ (prefixWord ++ tailWord_785391).sum := by decide
  have hdescent : baseEnd_785391 < baseStart_785391 := by decide
  rcases family_descends (prefixWord ++ tailWord_785391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785397 : List Nat := [1, 3, 5, 2, 1, 2, 1, 3, 4]
def baseStart_785397 : Nat := 118140960795 + 785397 * 2 ^ 59
def prefixEnd_785397 : Nat := 4983230072969 + 3 ^ 40 * 785397 * 2
def baseEnd_785397 : Nat := 89619147910970858739007

theorem tailTrace_785397 : CollatzResearch.WordTrace tailWord_785397 prefixEnd_785397 89619147910970858739007 := by
  unfold tailWord_785397
  simp only [CollatzResearch.WordTrace]
  refine ⟨28645781935648278973666445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19097187957098852649110963 28645781935648278973666445)
  ·
    refine ⟨10742168225868104615124917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28645781935648278973666445 10742168225868104615124917)
    ·
      refine ⟨1007078271175134807667961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10742168225868104615124917 1007078271175134807667961)
      ·
        refine ⟨755308703381351105750971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1007078271175134807667961 755308703381351105750971)
        ·
          refine ⟨1132963055072026658626457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 755308703381351105750971 1132963055072026658626457)
          ·
            refine ⟨849722291304019993969843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1132963055072026658626457 849722291304019993969843)
            ·
              refine ⟨1274583436956029990954765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 849722291304019993969843 1274583436956029990954765)
              ·
                refine ⟨477968788858511246608037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1274583436956029990954765 477968788858511246608037)
                ·
                  refine ⟨89619147910970858739007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 477968788858511246608037 89619147910970858739007)
                  ·
                    rfl

theorem cell22_785397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 3, 4].length) (baseStart_785397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_785397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_785397 prefixEnd_785397 := by exact prefixLift 785397
  have htrace : WordTrace (prefixWord ++ tailWord_785397) baseStart_785397 baseEnd_785397 := by
    simpa [prefixWord, tailWord_785397, baseEnd_785397] using wordTrace_append hprefix tailTrace_785397
  have hstable : (prefixWord ++ tailWord_785397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785397).length < 2 ^ (prefixWord ++ tailWord_785397).sum := by decide
  have hdescent : baseEnd_785397 < baseStart_785397 := by decide
  rcases family_descends (prefixWord ++ tailWord_785397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785410 : List Nat := [3, 4, 1, 3, 1, 1, 1, 2, 2, 4]
def baseStart_785410 : Nat := 118140960795 + 785410 * 2 ^ 59
def prefixEnd_785410 : Nat := 4983230072969 + 3 ^ 40 * 785410 * 2
def baseEnd_785410 : Nat := 268861893898584875641981

theorem tailTrace_785410 : CollatzResearch.WordTrace tailWord_785410 prefixEnd_785410 268861893898584875641981 := by
  unfold tailWord_785410
  simp only [CollatzResearch.WordTrace]
  refine ⟨7161564021150295548472421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19097504056400788129259789 7161564021150295548472421)
  ·
    refine ⟨1342793253965680415338579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7161564021150295548472421 1342793253965680415338579)
    ·
      refine ⟨2014189880948520623007869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1342793253965680415338579 2014189880948520623007869)
      ·
        refine ⟨755321205355695233627951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2014189880948520623007869 755321205355695233627951)
        ·
          refine ⟨1132981808033542850441927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 755321205355695233627951 1132981808033542850441927)
          ·
            refine ⟨1699472712050314275662891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1132981808033542850441927 1699472712050314275662891)
            ·
              refine ⟨2549209068075471413494337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1699472712050314275662891 2549209068075471413494337)
              ·
                refine ⟨1911906801056603560120753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2549209068075471413494337 1911906801056603560120753)
                ·
                  refine ⟨1433930100792452670090565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1911906801056603560120753 1433930100792452670090565)
                  ·
                    refine ⟨268861893898584875641981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1433930100792452670090565 268861893898584875641981)
                    ·
                      rfl

theorem cell22_785410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_785410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_785410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_785410 prefixEnd_785410 := by exact prefixLift 785410
  have htrace : WordTrace (prefixWord ++ tailWord_785410) baseStart_785410 baseEnd_785410 := by
    simpa [prefixWord, tailWord_785410, baseEnd_785410] using wordTrace_append hprefix tailTrace_785410
  have hstable : (prefixWord ++ tailWord_785410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785410).length < 2 ^ (prefixWord ++ tailWord_785410).sum := by decide
  have hdescent : baseEnd_785410 < baseStart_785410 := by decide
  rcases family_descends (prefixWord ++ tailWord_785410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785419 : List Nat := [1, 1, 1, 1, 6, 2, 2, 1, 7]
def baseStart_785419 : Nat := 118140960795 + 785419 * 2 ^ 59
def prefixEnd_785419 : Nat := 4983230072969 + 3 ^ 40 * 785419 * 2
def baseEnd_785419 : Nat := 89621658260837284055651

theorem tailTrace_785419 : CollatzResearch.WordTrace tailWord_785419 prefixEnd_785419 89621658260837284055651 := by
  unfold tailWord_785419
  simp only [CollatzResearch.WordTrace]
  refine ⟨28646584341568576730967311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19097722894379051153978207 28646584341568576730967311)
  ·
    refine ⟨42969876512352865096450967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28646584341568576730967311 42969876512352865096450967)
    ·
      refine ⟨64454814768529297644676451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42969876512352865096450967 64454814768529297644676451)
      ·
        refine ⟨96682222152793946467014677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64454814768529297644676451 96682222152793946467014677)
        ·
          refine ⟨4531979163412216240641313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 96682222152793946467014677 4531979163412216240641313)
          ·
            refine ⟨3398984372559162180480985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4531979163412216240641313 3398984372559162180480985)
            ·
              refine ⟨2549238279419371635360739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3398984372559162180480985 2549238279419371635360739)
              ·
                refine ⟨3823857419129057453041109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2549238279419371635360739 3823857419129057453041109)
                ·
                  refine ⟨89621658260837284055651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3823857419129057453041109 89621658260837284055651)
                  ·
                    rfl

theorem cell22_785419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 7].length) (baseStart_785419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_785419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_785419 prefixEnd_785419 := by exact prefixLift 785419
  have htrace : WordTrace (prefixWord ++ tailWord_785419) baseStart_785419 baseEnd_785419 := by
    simpa [prefixWord, tailWord_785419, baseEnd_785419] using wordTrace_append hprefix tailTrace_785419
  have hstable : (prefixWord ++ tailWord_785419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785419).length < 2 ^ (prefixWord ++ tailWord_785419).sum := by decide
  have hdescent : baseEnd_785419 < baseStart_785419 := by decide
  rcases family_descends (prefixWord ++ tailWord_785419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785434 : List Nat := [3, 1, 1, 3, 1, 2, 2, 1, 1, 7]
def baseStart_785434 : Nat := 118140960795 + 785434 * 2 ^ 59
def prefixEnd_785434 : Nat := 4983230072969 + 3 ^ 40 * 785434 * 2
def baseEnd_785434 : Nat := 268870109589056813041907

theorem tailTrace_785434 : CollatzResearch.WordTrace tailWord_785434 prefixEnd_785434 268870109589056813041907 := by
  unfold tailWord_785434
  simp only [CollatzResearch.WordTrace]
  refine ⟨7161782859128558573190839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19098087624342822861842237 7161782859128558573190839)
  ·
    refine ⟨10742674288692837859786259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7161782859128558573190839 10742674288692837859786259)
    ·
      refine ⟨16114011433039256789679389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10742674288692837859786259 16114011433039256789679389)
      ·
        refine ⟨6042754287389721296129771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16114011433039256789679389 6042754287389721296129771)
        ·
          refine ⟨9064131431084581944194657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6042754287389721296129771 9064131431084581944194657)
          ·
            refine ⟨6798098573313436458145993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9064131431084581944194657 6798098573313436458145993)
            ·
              refine ⟨5098573929985077343609495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6798098573313436458145993 5098573929985077343609495)
              ·
                refine ⟨7647860894977616015414243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5098573929985077343609495 7647860894977616015414243)
                ·
                  refine ⟨11471791342466424023121365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7647860894977616015414243 11471791342466424023121365)
                  ·
                    refine ⟨268870109589056813041907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11471791342466424023121365 268870109589056813041907)
                    ·
                      rfl

theorem cell22_785434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 1, 7].length) (baseStart_785434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_785434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_785434 prefixEnd_785434 := by exact prefixLift 785434
  have htrace : WordTrace (prefixWord ++ tailWord_785434) baseStart_785434 baseEnd_785434 := by
    simpa [prefixWord, tailWord_785434, baseEnd_785434] using wordTrace_append hprefix tailTrace_785434
  have hstable : (prefixWord ++ tailWord_785434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785434).length < 2 ^ (prefixWord ++ tailWord_785434).sum := by decide
  have hdescent : baseEnd_785434 < baseStart_785434 := by decide
  rcases family_descends (prefixWord ++ tailWord_785434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785466 : List Nat := [3, 1, 1, 1, 3, 1, 2, 5, 1, 4]
def baseStart_785466 : Nat := 118140960795 + 785466 * 2 ^ 59
def prefixEnd_785466 : Nat := 4983230072969 + 3 ^ 40 * 785466 * 2
def baseEnd_785466 : Nat := 268881063843019396241809

theorem tailTrace_785466 : CollatzResearch.WordTrace tailWord_785466 prefixEnd_785466 268881063843019396241809 := by
  unfold tailWord_785466
  simp only [CollatzResearch.WordTrace]
  refine ⟨7162074643099575939482063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19098865714932202505285501 7162074643099575939482063)
  ·
    refine ⟨10743111964649363909223095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7162074643099575939482063 10743111964649363909223095)
    ·
      refine ⟨16114667946974045863834643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10743111964649363909223095 16114667946974045863834643)
      ·
        refine ⟨24172001920461068795751965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16114667946974045863834643 24172001920461068795751965)
        ·
          refine ⟨9064500720172900798406987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24172001920461068795751965 9064500720172900798406987)
          ·
            refine ⟨13596751080259351197610481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9064500720172900798406987 13596751080259351197610481)
            ·
              refine ⟨10197563310194513398207861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13596751080259351197610481 10197563310194513398207861)
              ·
                refine ⟨956021560330735631081987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10197563310194513398207861 956021560330735631081987)
                ·
                  refine ⟨1434032340496103446622981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 956021560330735631081987 1434032340496103446622981)
                  ·
                    refine ⟨268881063843019396241809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1434032340496103446622981 268881063843019396241809)
                    ·
                      rfl

theorem cell22_785466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 5, 1, 4].length) (baseStart_785466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_785466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_785466 prefixEnd_785466 := by exact prefixLift 785466
  have htrace : WordTrace (prefixWord ++ tailWord_785466) baseStart_785466 baseEnd_785466 := by
    simpa [prefixWord, tailWord_785466, baseEnd_785466] using wordTrace_append hprefix tailTrace_785466
  have hstable : (prefixWord ++ tailWord_785466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785466).length < 2 ^ (prefixWord ++ tailWord_785466).sum := by decide
  have hdescent : baseEnd_785466 < baseStart_785466 := by decide
  rcases family_descends (prefixWord ++ tailWord_785466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785496 : List Nat := [2, 1, 2, 2, 1, 3, 4, 1, 1, 5]
def baseStart_785496 : Nat := 118140960795 + 785496 * 2 ^ 59
def prefixEnd_785496 : Nat := 4983230072969 + 3 ^ 40 * 785496 * 2
def baseEnd_785496 : Nat := 268891333456109317991717

theorem tailTrace_785496 : CollatzResearch.WordTrace tailWord_785496 prefixEnd_785496 268891333456109317991717 := by
  unfold tailWord_785496
  simp only [CollatzResearch.WordTrace]
  refine ⟨14324696381144809440760171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19099595174859745921013561 14324696381144809440760171)
  ·
    refine ⟨21487044571717214161140257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14324696381144809440760171 21487044571717214161140257)
    ·
      refine ⟨16115283428787910620855193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21487044571717214161140257 16115283428787910620855193)
      ·
        refine ⟨12086462571590932965641395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16115283428787910620855193 12086462571590932965641395)
        ·
          refine ⟨18129693857386399448462093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12086462571590932965641395 18129693857386399448462093)
          ·
            refine ⟨6798635196519899793173285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18129693857386399448462093 6798635196519899793173285)
            ·
              refine ⟨1274744099347481211219991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6798635196519899793173285 1274744099347481211219991)
              ·
                refine ⟨1912116149021221816829987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1274744099347481211219991 1912116149021221816829987)
                ·
                  refine ⟨2868174223531832725244981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1912116149021221816829987 2868174223531832725244981)
                  ·
                    refine ⟨268891333456109317991717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2868174223531832725244981 268891333456109317991717)
                    ·
                      rfl

theorem cell22_785496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 1, 5].length) (baseStart_785496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_785496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_785496 prefixEnd_785496 := by exact prefixLift 785496
  have htrace : WordTrace (prefixWord ++ tailWord_785496) baseStart_785496 baseEnd_785496 := by
    simpa [prefixWord, tailWord_785496, baseEnd_785496] using wordTrace_append hprefix tailTrace_785496
  have hstable : (prefixWord ++ tailWord_785496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785496).length < 2 ^ (prefixWord ++ tailWord_785496).sum := by decide
  have hdescent : baseEnd_785496 < baseStart_785496 := by decide
  rcases family_descends (prefixWord ++ tailWord_785496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785511 : List Nat := [1, 1, 5, 1, 1, 4, 1, 1, 1, 6]
def baseStart_785511 : Nat := 118140960795 + 785511 * 2 ^ 59
def prefixEnd_785511 : Nat := 4983230072969 + 3 ^ 40 * 785511 * 2
def baseEnd_785511 : Nat := 268896468262654278866671

theorem tailTrace_785511 : CollatzResearch.WordTrace tailWord_785511 prefixEnd_785511 268896468262654278866671 := by
  unfold tailWord_785511
  simp only [CollatzResearch.WordTrace]
  refine ⟨28649939857235276443316387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19099959904823517628877591 28649939857235276443316387)
  ·
    refine ⟨42974909785852914664974581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28649939857235276443316387 42974909785852914664974581)
    ·
      refine ⟨4028897792423710749841367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42974909785852914664974581 4028897792423710749841367)
      ·
        refine ⟨6043346688635566124762051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4028897792423710749841367 6043346688635566124762051)
        ·
          refine ⟨9065020032953349187143077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6043346688635566124762051 9065020032953349187143077)
          ·
            refine ⟨1699691256178752972589327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9065020032953349187143077 1699691256178752972589327)
            ·
              refine ⟨2549536884268129458883991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1699691256178752972589327 2549536884268129458883991)
              ·
                refine ⟨3824305326402194188325987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2549536884268129458883991 3824305326402194188325987)
                ·
                  refine ⟨5736457989603291282488981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3824305326402194188325987 5736457989603291282488981)
                  ·
                    refine ⟨268896468262654278866671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5736457989603291282488981 268896468262654278866671)
                    ·
                      rfl

theorem cell22_785511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_785511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_785511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_785511 prefixEnd_785511 := by exact prefixLift 785511
  have htrace : WordTrace (prefixWord ++ tailWord_785511) baseStart_785511 baseEnd_785511 := by
    simpa [prefixWord, tailWord_785511, baseEnd_785511] using wordTrace_append hprefix tailTrace_785511
  have hstable : (prefixWord ++ tailWord_785511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785511).length < 2 ^ (prefixWord ++ tailWord_785511).sum := by decide
  have hdescent : baseEnd_785511 < baseStart_785511 := by decide
  rcases family_descends (prefixWord ++ tailWord_785511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785526 : List Nat := [5, 1, 1, 2, 1, 1, 11]
def baseStart_785526 : Nat := 118140960795 + 785526 * 2 ^ 59
def prefixEnd_785526 : Nat := 4983230072969 + 3 ^ 40 * 785526 * 2
def baseEnd_785526 : Nat := 9959318632192564434875

theorem tailTrace_785526 : CollatzResearch.WordTrace tailWord_785526 prefixEnd_785526 9959318632192564434875 := by
  unfold tailWord_785526
  simp only [CollatzResearch.WordTrace]
  refine ⟨1790655434511308375319527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19100324634787289336741621 1790655434511308375319527)
  ·
    refine ⟨2685983151766962562979291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1790655434511308375319527 2685983151766962562979291)
    ·
      refine ⟨4028974727650443844468937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2685983151766962562979291 4028974727650443844468937)
      ·
        refine ⟨3021731045737832883351703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4028974727650443844468937 3021731045737832883351703)
        ·
          refine ⟨4532596568606749325027555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3021731045737832883351703 4532596568606749325027555)
          ·
            refine ⟨6798894852910123987541333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4532596568606749325027555 6798894852910123987541333)
            ·
              refine ⟨9959318632192564434875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 6798894852910123987541333 9959318632192564434875)
              ·
                rfl

theorem cell22_785526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 11].length) (baseStart_785526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_785526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_785526 prefixEnd_785526 := by exact prefixLift 785526
  have htrace : WordTrace (prefixWord ++ tailWord_785526) baseStart_785526 baseEnd_785526 := by
    simpa [prefixWord, tailWord_785526, baseEnd_785526] using wordTrace_append hprefix tailTrace_785526
  have hstable : (prefixWord ++ tailWord_785526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785526).length < 2 ^ (prefixWord ++ tailWord_785526).sum := by decide
  have hdescent : baseEnd_785526 < baseStart_785526 := by decide
  rcases family_descends (prefixWord ++ tailWord_785526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785618 : List Nat := [3, 2, 2, 2, 1, 1, 3, 1, 3, 4]
def baseStart_785618 : Nat := 118140960795 + 785618 * 2 ^ 59
def prefixEnd_785618 : Nat := 4983230072969 + 3 ^ 40 * 785618 * 2
def baseEnd_785618 : Nat := 268933096549341666441343

theorem tailTrace_785618 : CollatzResearch.WordTrace tailWord_785618 prefixEnd_785618 268933096549341666441343 := by
  unfold tailWord_785618
  simp only [CollatzResearch.WordTrace]
  refine ⟨7163460616961908429365377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19102561645231755811641005 7163460616961908429365377)
  ·
    refine ⟨5372595462721431322024033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7163460616961908429365377 5372595462721431322024033)
    ·
      refine ⟨4029446597041073491518025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5372595462721431322024033 4029446597041073491518025)
      ·
        refine ⟨3022084947780805118638519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4029446597041073491518025 3022084947780805118638519)
        ·
          refine ⟨4533127421671207677957779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3022084947780805118638519 4533127421671207677957779)
          ·
            refine ⟨6799691132506811516936669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4533127421671207677957779 6799691132506811516936669)
            ·
              refine ⟨2549884174690054318851251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6799691132506811516936669 2549884174690054318851251)
              ·
                refine ⟨3824826262035081478276877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2549884174690054318851251 3824826262035081478276877)
                ·
                  refine ⟨1434309848263155554353829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3824826262035081478276877 1434309848263155554353829)
                  ·
                    refine ⟨268933096549341666441343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1434309848263155554353829 268933096549341666441343)
                    ·
                      rfl

theorem cell22_785618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_785618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_785618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_785618 prefixEnd_785618 := by exact prefixLift 785618
  have htrace : WordTrace (prefixWord ++ tailWord_785618) baseStart_785618 baseEnd_785618 := by
    simpa [prefixWord, tailWord_785618, baseEnd_785618] using wordTrace_append hprefix tailTrace_785618
  have hstable : (prefixWord ++ tailWord_785618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785618).length < 2 ^ (prefixWord ++ tailWord_785618).sum := by decide
  have hdescent : baseEnd_785618 < baseStart_785618 := by decide
  rcases family_descends (prefixWord ++ tailWord_785618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785631 : List Nat := [1, 1, 2, 3, 2, 1, 3, 1, 3, 5]
def baseStart_785631 : Nat := 118140960795 + 785631 * 2 ^ 59
def prefixEnd_785631 : Nat := 4983230072969 + 3 ^ 40 * 785631 * 2
def baseEnd_785631 : Nat := 268937546715013965866303

theorem tailTrace_785631 : CollatzResearch.WordTrace tailWord_785631 prefixEnd_785631 268937546715013965866303 := by
  unfold tailWord_785631
  simp only [CollatzResearch.WordTrace]
  refine ⟨28654316616800536937684747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19102877744533691291789831 28654316616800536937684747)
  ·
    refine ⟨42981474925200805406527121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28654316616800536937684747 42981474925200805406527121)
    ·
      refine ⟨32236106193900604054895341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42981474925200805406527121 32236106193900604054895341)
      ·
        refine ⟨12088539822712726520585753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32236106193900604054895341 12088539822712726520585753)
        ·
          refine ⟨9066404867034544890439315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12088539822712726520585753 9066404867034544890439315)
          ·
            refine ⟨13599607300551817335658973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9066404867034544890439315 13599607300551817335658973)
            ·
              refine ⟨5099852737706931500872115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13599607300551817335658973 5099852737706931500872115)
              ·
                refine ⟨7649779106560397251308173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5099852737706931500872115 7649779106560397251308173)
                ·
                  refine ⟨2868667164960148969240565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7649779106560397251308173 2868667164960148969240565)
                  ·
                    refine ⟨268937546715013965866303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2868667164960148969240565 268937546715013965866303)
                    ·
                      rfl

theorem cell22_785631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 5].length) (baseStart_785631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_785631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_785631 prefixEnd_785631 := by exact prefixLift 785631
  have htrace : WordTrace (prefixWord ++ tailWord_785631) baseStart_785631 baseEnd_785631 := by
    simpa [prefixWord, tailWord_785631, baseEnd_785631] using wordTrace_append hprefix tailTrace_785631
  have hstable : (prefixWord ++ tailWord_785631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785631).length < 2 ^ (prefixWord ++ tailWord_785631).sum := by decide
  have hdescent : baseEnd_785631 < baseStart_785631 := by decide
  rcases family_descends (prefixWord ++ tailWord_785631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785665 : List Nat := [1, 2, 4, 1, 1, 3, 2, 3, 2, 3]
def baseStart_785665 : Nat := 118140960795 + 785665 * 2 ^ 59
def prefixEnd_785665 : Nat := 4983230072969 + 3 ^ 40 * 785665 * 2
def baseEnd_785665 : Nat := 268949185609849210516199

theorem tailTrace_785665 : CollatzResearch.WordTrace tailWord_785665 prefixEnd_785665 268949185609849210516199 := by
  unfold tailWord_785665
  simp only [CollatzResearch.WordTrace]
  refine ⟨28655556698677360744422449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19103704465784907162948299 28655556698677360744422449)
  ·
    refine ⟨21491667524008020558316837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28655556698677360744422449 21491667524008020558316837)
    ·
      refine ⟨4029687660751503854684407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21491667524008020558316837 4029687660751503854684407)
      ·
        refine ⟨6044531491127255782026611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4029687660751503854684407 6044531491127255782026611)
        ·
          refine ⟨9066797236690883673039917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6044531491127255782026611 9066797236690883673039917)
          ·
            refine ⟨3400048963759081377389969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9066797236690883673039917 3400048963759081377389969)
            ·
              refine ⟨2550036722819311033042477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3400048963759081377389969 2550036722819311033042477)
              ·
                refine ⟨956263771057241637390929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2550036722819311033042477 956263771057241637390929)
                ·
                  refine ⟨717197828292931228043197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 956263771057241637390929 717197828292931228043197)
                  ·
                    refine ⟨268949185609849210516199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 717197828292931228043197 268949185609849210516199)
                    ·
                      rfl

theorem cell22_785665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_785665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_785665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_785665 prefixEnd_785665 := by exact prefixLift 785665
  have htrace : WordTrace (prefixWord ++ tailWord_785665) baseStart_785665 baseEnd_785665 := by
    simpa [prefixWord, tailWord_785665, baseEnd_785665] using wordTrace_append hprefix tailTrace_785665
  have hstable : (prefixWord ++ tailWord_785665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785665).length < 2 ^ (prefixWord ++ tailWord_785665).sum := by decide
  have hdescent : baseEnd_785665 < baseStart_785665 := by decide
  rcases family_descends (prefixWord ++ tailWord_785665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785783 : List Nat := [1, 1, 3, 1, 1, 2, 4, 3, 1, 5]
def baseStart_785783 : Nat := 118140960795 + 785783 * 2 ^ 59
def prefixEnd_785783 : Nat := 4983230072969 + 3 ^ 40 * 785783 * 2
def baseEnd_785783 : Nat := 268989579421336236065837

theorem tailTrace_785783 : CollatzResearch.WordTrace tailWord_785783 prefixEnd_785783 268989579421336236065837 := by
  unfold tailWord_785783
  simp only [CollatzResearch.WordTrace]
  refine ⟨28659860512249866897218003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19106573674833244598145335 28659860512249866897218003)
  ·
    refine ⟨42989790768374800345827005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28659860512249866897218003 42989790768374800345827005)
    ·
      refine ⟨16121171538140550129685127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42989790768374800345827005 16121171538140550129685127)
      ·
        refine ⟨24181757307210825194527691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16121171538140550129685127 24181757307210825194527691)
        ·
          refine ⟨36272635960816237791791537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24181757307210825194527691 36272635960816237791791537)
          ·
            refine ⟨27204476970612178343843653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36272635960816237791791537 27204476970612178343843653)
            ·
              refine ⟨5100839431989783439470685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27204476970612178343843653 5100839431989783439470685)
              ·
                refine ⟨1912814786996168789801507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5100839431989783439470685 1912814786996168789801507)
                ·
                  refine ⟨2869222180494253184702261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1912814786996168789801507 2869222180494253184702261)
                  ·
                    refine ⟨268989579421336236065837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2869222180494253184702261 268989579421336236065837)
                    ·
                      rfl

theorem cell22_785783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 5].length) (baseStart_785783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_785783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_785783 prefixEnd_785783 := by exact prefixLift 785783
  have htrace : WordTrace (prefixWord ++ tailWord_785783) baseStart_785783 baseEnd_785783 := by
    simpa [prefixWord, tailWord_785783, baseEnd_785783] using wordTrace_append hprefix tailTrace_785783
  have hstable : (prefixWord ++ tailWord_785783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785783).length < 2 ^ (prefixWord ++ tailWord_785783).sum := by decide
  have hdescent : baseEnd_785783 < baseStart_785783 := by decide
  rcases family_descends (prefixWord ++ tailWord_785783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785800 : List Nat := [2, 1, 3, 3, 1, 3, 1, 2, 1, 5]
def baseStart_785800 : Nat := 118140960795 + 785800 * 2 ^ 59
def prefixEnd_785800 : Nat := 4983230072969 + 3 ^ 40 * 785800 * 2
def baseEnd_785800 : Nat := 268995398868753858390785

theorem tailTrace_785800 : CollatzResearch.WordTrace tailWord_785800 prefixEnd_785800 268995398868753858390785 := by
  unfold tailWord_785800
  simp only [CollatzResearch.WordTrace]
  refine ⟨14330240276594139400293427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19106987035458852533724569 14330240276594139400293427)
  ·
    refine ⟨21495360414891209100440141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14330240276594139400293427 21495360414891209100440141)
    ·
      refine ⟨8060760155584203412665053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21495360414891209100440141 8060760155584203412665053)
      ·
        refine ⟨3022785058344076279749395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8060760155584203412665053 3022785058344076279749395)
        ·
          refine ⟨4534177587516114419624093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3022785058344076279749395 4534177587516114419624093)
          ·
            refine ⟨1700316595318542907359035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4534177587516114419624093 1700316595318542907359035)
            ·
              refine ⟨2550474892977814361038553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1700316595318542907359035 2550474892977814361038553)
              ·
                refine ⟨1912856169733360770778915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2550474892977814361038553 1912856169733360770778915)
                ·
                  refine ⟨2869284254600041156168373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1912856169733360770778915 2869284254600041156168373)
                  ·
                    refine ⟨268995398868753858390785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2869284254600041156168373 268995398868753858390785)
                    ·
                      rfl

theorem cell22_785800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_785800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_785800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_785800 prefixEnd_785800 := by exact prefixLift 785800
  have htrace : WordTrace (prefixWord ++ tailWord_785800) baseStart_785800 baseEnd_785800 := by
    simpa [prefixWord, tailWord_785800, baseEnd_785800] using wordTrace_append hprefix tailTrace_785800
  have hstable : (prefixWord ++ tailWord_785800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785800).length < 2 ^ (prefixWord ++ tailWord_785800).sum := by decide
  have hdescent : baseEnd_785800 < baseStart_785800 := by decide
  rcases family_descends (prefixWord ++ tailWord_785800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785817 : List Nat := [1, 2, 1, 2, 1, 6, 2, 2, 2, 3]
def baseStart_785817 : Nat := 118140960795 + 785817 * 2 ^ 59
def prefixEnd_785817 : Nat := 4983230072969 + 3 ^ 40 * 785817 * 2
def baseEnd_785817 : Nat := 269001218316171480715733

theorem tailTrace_785817 : CollatzResearch.WordTrace tailWord_785817 prefixEnd_785817 269001218316171480715733 := by
  unfold tailWord_785817
  simp only [CollatzResearch.WordTrace]
  refine ⟨28661100594126690703955705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19107400396084460469303803 28661100594126690703955705)
  ·
    refine ⟨21495825445595018027966779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28661100594126690703955705 21495825445595018027966779)
    ·
      refine ⟨32243738168392527041950169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21495825445595018027966779 32243738168392527041950169)
      ·
        refine ⟨24182803626294395281462627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32243738168392527041950169 24182803626294395281462627)
        ·
          refine ⟨36274205439441592922193941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24182803626294395281462627 36274205439441592922193941)
          ·
            refine ⟨1700353379973824668227841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 36274205439441592922193941 1700353379973824668227841)
            ·
              refine ⟨1275265034980368501170881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1700353379973824668227841 1275265034980368501170881)
              ·
                refine ⟨956448776235276375878161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1275265034980368501170881 956448776235276375878161)
                ·
                  refine ⟨717336582176457281908621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 956448776235276375878161 717336582176457281908621)
                  ·
                    refine ⟨269001218316171480715733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 717336582176457281908621 269001218316171480715733)
                    ·
                      rfl

theorem cell22_785817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 2, 2, 3].length) (baseStart_785817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_785817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_785817 prefixEnd_785817 := by exact prefixLift 785817
  have htrace : WordTrace (prefixWord ++ tailWord_785817) baseStart_785817 baseEnd_785817 := by
    simpa [prefixWord, tailWord_785817, baseEnd_785817] using wordTrace_append hprefix tailTrace_785817
  have hstable : (prefixWord ++ tailWord_785817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785817).length < 2 ^ (prefixWord ++ tailWord_785817).sum := by decide
  have hdescent : baseEnd_785817 < baseStart_785817 := by decide
  rcases family_descends (prefixWord ++ tailWord_785817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785828 : List Nat := [2, 3, 1, 2, 1, 1, 1, 2, 2, 7]
def baseStart_785828 : Nat := 118140960795 + 785828 * 2 ^ 59
def prefixEnd_785828 : Nat := 4983230072969 + 3 ^ 40 * 785828 * 2
def baseEnd_785828 : Nat := 269004983840971118690699

theorem tailTrace_785828 : CollatzResearch.WordTrace tailWord_785828 prefixEnd_785828 269004983840971118690699 := by
  unfold tailWord_785828
  simp only [CollatzResearch.WordTrace]
  refine ⟨14330750898543419791303069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19107667864724559721737425 14330750898543419791303069)
  ·
    refine ⟨5374031586953782421738651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14330750898543419791303069 5374031586953782421738651)
    ·
      refine ⟨8061047380430673632607977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5374031586953782421738651 8061047380430673632607977)
      ·
        refine ⟨6045785535323005224455983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8061047380430673632607977 6045785535323005224455983)
        ·
          refine ⟨9068678302984507836683975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6045785535323005224455983 9068678302984507836683975)
          ·
            refine ⟨13603017454476761755025963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9068678302984507836683975 13603017454476761755025963)
            ·
              refine ⟨20404526181715142632538945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13603017454476761755025963 20404526181715142632538945)
              ·
                refine ⟨15303394636286356974404209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20404526181715142632538945 15303394636286356974404209)
                ·
                  refine ⟨11477545977214767730803157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15303394636286356974404209 11477545977214767730803157)
                  ·
                    refine ⟨269004983840971118690699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11477545977214767730803157 269004983840971118690699)
                    ·
                      rfl

theorem cell22_785828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_785828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_785828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_785828 prefixEnd_785828 := by exact prefixLift 785828
  have htrace : WordTrace (prefixWord ++ tailWord_785828) baseStart_785828 baseEnd_785828 := by
    simpa [prefixWord, tailWord_785828, baseEnd_785828] using wordTrace_append hprefix tailTrace_785828
  have hstable : (prefixWord ++ tailWord_785828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785828).length < 2 ^ (prefixWord ++ tailWord_785828).sum := by decide
  have hdescent : baseEnd_785828 < baseStart_785828 := by decide
  rcases family_descends (prefixWord ++ tailWord_785828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785849 : List Nat := [1, 2, 1, 4, 5, 1, 1, 1, 2, 4]
def baseStart_785849 : Nat := 118140960795 + 785849 * 2 ^ 59
def prefixEnd_785849 : Nat := 4983230072969 + 3 ^ 40 * 785849 * 2
def baseEnd_785849 : Nat := 269012172570134063915635

theorem tailTrace_785849 : CollatzResearch.WordTrace tailWord_785849 prefixEnd_785849 269012172570134063915635 := by
  unfold tailWord_785849
  simp only [CollatzResearch.WordTrace]
  refine ⟨28662267730010760169120601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19108178486673840112747067 28662267730010760169120601)
  ·
    refine ⟨21496700797508070126840451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28662267730010760169120601 21496700797508070126840451)
    ·
      refine ⟨32245051196262105190260677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21496700797508070126840451 32245051196262105190260677)
      ·
        refine ⟨6045947099299144723173877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32245051196262105190260677 6045947099299144723173877)
        ·
          refine ⟨566807540559294817797551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6045947099299144723173877 566807540559294817797551)
          ·
            refine ⟨850211310838942226696327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 566807540559294817797551 850211310838942226696327)
            ·
              refine ⟨1275316966258413340044491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 850211310838942226696327 1275316966258413340044491)
              ·
                refine ⟨1912975449387620010066737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1275316966258413340044491 1912975449387620010066737)
                ·
                  refine ⟨1434731587040715007550053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1912975449387620010066737 1434731587040715007550053)
                  ·
                    refine ⟨269012172570134063915635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1434731587040715007550053 269012172570134063915635)
                    ·
                      rfl

theorem cell22_785849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 2, 4].length) (baseStart_785849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_785849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_785849 prefixEnd_785849 := by exact prefixLift 785849
  have htrace : WordTrace (prefixWord ++ tailWord_785849) baseStart_785849 baseEnd_785849 := by
    simpa [prefixWord, tailWord_785849, baseEnd_785849] using wordTrace_append hprefix tailTrace_785849
  have hstable : (prefixWord ++ tailWord_785849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785849).length < 2 ^ (prefixWord ++ tailWord_785849).sum := by decide
  have hdescent : baseEnd_785849 < baseStart_785849 := by decide
  rcases family_descends (prefixWord ++ tailWord_785849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785888 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 2, 8]
def baseStart_785888 : Nat := 118140960795 + 785888 * 2 ^ 59
def prefixEnd_785888 : Nat := 4983230072969 + 3 ^ 40 * 785888 * 2
def baseEnd_785888 : Nat := 269025523067150962190515

theorem tailTrace_785888 : CollatzResearch.WordTrace tailWord_785888 prefixEnd_785888 269025523067150962190515 := by
  unfold tailWord_785888
  simp only [CollatzResearch.WordTrace]
  refine ⟨14331845088434734914895159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19109126784579646553193545 14331845088434734914895159)
  ·
    refine ⟨21497767632652102372342739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14331845088434734914895159 21497767632652102372342739)
    ·
      refine ⟨32246651448978153558514109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21497767632652102372342739 32246651448978153558514109)
      ·
        refine ⟨12092494293366807584442791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32246651448978153558514109 12092494293366807584442791)
        ·
          refine ⟨18138741440050211376664187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12092494293366807584442791 18138741440050211376664187)
          ·
            refine ⟨27208112160075317064996281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18138741440050211376664187 27208112160075317064996281)
            ·
              refine ⟨20406084120056487798747211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27208112160075317064996281 20406084120056487798747211)
              ·
                refine ⟨30609126180084731698120817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20406084120056487798747211 30609126180084731698120817)
                ·
                  refine ⟨22956844635063548773590613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30609126180084731698120817 22956844635063548773590613)
                  ·
                    refine ⟨269025523067150962190515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 22956844635063548773590613 269025523067150962190515)
                    ·
                      rfl

theorem cell22_785888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 2, 8].length) (baseStart_785888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_785888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_785888 prefixEnd_785888 := by exact prefixLift 785888
  have htrace : WordTrace (prefixWord ++ tailWord_785888) baseStart_785888 baseEnd_785888 := by
    simpa [prefixWord, tailWord_785888, baseEnd_785888] using wordTrace_append hprefix tailTrace_785888
  have hstable : (prefixWord ++ tailWord_785888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785888).length < 2 ^ (prefixWord ++ tailWord_785888).sum := by decide
  have hdescent : baseEnd_785888 < baseStart_785888 := by decide
  rcases family_descends (prefixWord ++ tailWord_785888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785935 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 8, 3]
def baseStart_785935 : Nat := 118140960795 + 785935 * 2 ^ 59
def prefixEnd_785935 : Nat := 4983230072969 + 3 ^ 40 * 785935 * 2
def baseEnd_785935 : Nat := 269041612127658506265371

theorem tailTrace_785935 : CollatzResearch.WordTrace tailWord_785935 prefixEnd_785935 269041612127658506265371 := by
  unfold tailWord_785935
  simp only [CollatzResearch.WordTrace]
  refine ⟨28665404407699196856751259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19110269605132797904500839 28665404407699196856751259)
  ·
    refine ⟨42998106611548795285126889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28665404407699196856751259 42998106611548795285126889)
    ·
      refine ⟨32248579958661596463845167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42998106611548795285126889 32248579958661596463845167)
      ·
        refine ⟨48372869937992394695767751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32248579958661596463845167 48372869937992394695767751)
        ·
          refine ⟨72559304906988592043651627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48372869937992394695767751 72559304906988592043651627)
          ·
            refine ⟨108838957360482888065477441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72559304906988592043651627 108838957360482888065477441)
            ·
              refine ⟨81629218020362166049108081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108838957360482888065477441 81629218020362166049108081)
              ·
                refine ⟨61221913515271624536831061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81629218020362166049108081 61221913515271624536831061)
                ·
                  refine ⟨717444299007089350040989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 61221913515271624536831061 717444299007089350040989)
                  ·
                    refine ⟨269041612127658506265371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 717444299007089350040989 269041612127658506265371)
                    ·
                      rfl

theorem cell22_785935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 8, 3].length) (baseStart_785935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_785935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_785935 prefixEnd_785935 := by exact prefixLift 785935
  have htrace : WordTrace (prefixWord ++ tailWord_785935) baseStart_785935 baseEnd_785935 := by
    simpa [prefixWord, tailWord_785935, baseEnd_785935] using wordTrace_append hprefix tailTrace_785935
  have hstable : (prefixWord ++ tailWord_785935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785935).length < 2 ^ (prefixWord ++ tailWord_785935).sum := by decide
  have hdescent : baseEnd_785935 < baseStart_785935 := by decide
  rcases family_descends (prefixWord ++ tailWord_785935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786072 : List Nat := [2, 1, 2, 4, 1, 2, 2, 2, 6]
def baseStart_786072 : Nat := 118140960795 + 786072 * 2 ^ 59
def prefixEnd_786072 : Nat := 4983230072969 + 3 ^ 40 * 786072 * 2
def baseEnd_786072 : Nat := 89696170009145271863317

theorem tailTrace_786072 : CollatzResearch.WordTrace tailWord_786072 prefixEnd_786072 89696170009145271863317 := by
  unfold tailWord_786072
  simp only [CollatzResearch.WordTrace]
  refine ⟨14335200604101434627244235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19113600805468579502992313 14335200604101434627244235)
  ·
    refine ⟨21502800906152151940866353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14335200604101434627244235 21502800906152151940866353)
    ·
      refine ⟨16127100679614113955649765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21502800906152151940866353 16127100679614113955649765)
      ·
        refine ⟨3023831377427646366684331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16127100679614113955649765 3023831377427646366684331)
        ·
          refine ⟨4535747066141469550026497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3023831377427646366684331 4535747066141469550026497)
          ·
            refine ⟨3401810299606102162519873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4535747066141469550026497 3401810299606102162519873)
            ·
              refine ⟨2551357724704576621889905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3401810299606102162519873 2551357724704576621889905)
              ·
                refine ⟨1913518293528432466417429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2551357724704576621889905 1913518293528432466417429)
                ·
                  refine ⟨89696170009145271863317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1913518293528432466417429 89696170009145271863317)
                  ·
                    rfl

theorem cell22_786072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 6].length) (baseStart_786072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_786072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_786072 prefixEnd_786072 := by exact prefixLift 786072
  have htrace : WordTrace (prefixWord ++ tailWord_786072) baseStart_786072 baseEnd_786072 := by
    simpa [prefixWord, tailWord_786072, baseEnd_786072] using wordTrace_append hprefix tailTrace_786072
  have hstable : (prefixWord ++ tailWord_786072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786072).length < 2 ^ (prefixWord ++ tailWord_786072).sum := by decide
  have hdescent : baseEnd_786072 < baseStart_786072 := by decide
  rcases family_descends (prefixWord ++ tailWord_786072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786082 : List Nat := [3, 3, 1, 4, 2, 1, 1, 3, 1, 3]
def baseStart_786082 : Nat := 118140960795 + 786082 * 2 ^ 59
def prefixEnd_786082 : Nat := 4983230072969 + 3 ^ 40 * 786082 * 2
def baseEnd_786082 : Nat := 269091933231799122839921

theorem tailTrace_786082 : CollatzResearch.WordTrace tailWord_786082 prefixEnd_786082 269091933231799122839921 := by
  unfold tailWord_786082
  simp only [CollatzResearch.WordTrace]
  refine ⟨7167691484541660240588125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19113843958777760641568333 7167691484541660240588125)
  ·
    refine ⟨2687884306703122590220547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7167691484541660240588125 2687884306703122590220547)
    ·
      refine ⟨4031826460054683885330821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2687884306703122590220547 4031826460054683885330821)
      ·
        refine ⟨755967461260253228499529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4031826460054683885330821 755967461260253228499529)
        ·
          refine ⟨566975595945189921374647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 755967461260253228499529 566975595945189921374647)
          ·
            refine ⟨850463393917784882061971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 566975595945189921374647 850463393917784882061971)
            ·
              refine ⟨1275695090876677323092957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 850463393917784882061971 1275695090876677323092957)
              ·
                refine ⟨478385659078753996159859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1275695090876677323092957 478385659078753996159859)
                ·
                  refine ⟨717578488618130994239789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 478385659078753996159859 717578488618130994239789)
                  ·
                    refine ⟨269091933231799122839921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 717578488618130994239789 269091933231799122839921)
                    ·
                      rfl

theorem cell22_786082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_786082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_786082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_786082 prefixEnd_786082 := by exact prefixLift 786082
  have htrace : WordTrace (prefixWord ++ tailWord_786082) baseStart_786082 baseEnd_786082 := by
    simpa [prefixWord, tailWord_786082, baseEnd_786082] using wordTrace_append hprefix tailTrace_786082
  have hstable : (prefixWord ++ tailWord_786082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786082).length < 2 ^ (prefixWord ++ tailWord_786082).sum := by decide
  have hdescent : baseEnd_786082 < baseStart_786082 := by decide
  rcases family_descends (prefixWord ++ tailWord_786082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786106 : List Nat := [3, 1, 1, 1, 2, 5, 3, 2, 4]
def baseStart_786106 : Nat := 118140960795 + 786106 * 2 ^ 59
def prefixEnd_786106 : Nat := 4983230072969 + 3 ^ 40 * 786106 * 2
def baseEnd_786106 : Nat := 89700049640757020079949

theorem tailTrace_786106 : CollatzResearch.WordTrace tailWord_786106 prefixEnd_786106 89700049640757020079949 := by
  unfold tailWord_786106
  simp only [CollatzResearch.WordTrace]
  refine ⟨7167910322519923265306543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19114427526719795374150781 7167910322519923265306543)
  ·
    refine ⟨10751865483779884897959815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7167910322519923265306543 10751865483779884897959815)
    ·
      refine ⟨16127798225669827346939723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10751865483779884897959815 16127798225669827346939723)
      ·
        refine ⟨24191697338504741020409585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16127798225669827346939723 24191697338504741020409585)
        ·
          refine ⟨18143773003878555765307189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24191697338504741020409585 18143773003878555765307189)
          ·
            refine ⟨1700978719113614602997549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18143773003878555765307189 1700978719113614602997549)
            ·
              refine ⟨637867019667605476124081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1700978719113614602997549 637867019667605476124081)
              ·
                refine ⟨478400264750704107093061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 637867019667605476124081 478400264750704107093061)
                ·
                  refine ⟨89700049640757020079949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 478400264750704107093061 89700049640757020079949)
                  ·
                    rfl

theorem cell22_786106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 2, 4].length) (baseStart_786106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_786106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_786106 prefixEnd_786106 := by exact prefixLift 786106
  have htrace : WordTrace (prefixWord ++ tailWord_786106) baseStart_786106 baseEnd_786106 := by
    simpa [prefixWord, tailWord_786106, baseEnd_786106] using wordTrace_append hprefix tailTrace_786106
  have hstable : (prefixWord ++ tailWord_786106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786106).length < 2 ^ (prefixWord ++ tailWord_786106).sum := by decide
  have hdescent : baseEnd_786106 < baseStart_786106 := by decide
  rcases family_descends (prefixWord ++ tailWord_786106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786177 : List Nat := [1, 2, 4, 1, 1, 1, 3, 1, 1, 7]
def baseStart_786177 : Nat := 118140960795 + 786177 * 2 ^ 59
def prefixEnd_786177 : Nat := 4983230072969 + 3 ^ 40 * 786177 * 2
def baseEnd_786177 : Nat := 269124453673250541714629

theorem tailTrace_786177 : CollatzResearch.WordTrace tailWord_786177 prefixEnd_786177 269124453673250541714629 := by
  unfold tailWord_786177
  simp only [CollatzResearch.WordTrace]
  refine ⟨28674230872822472187060785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19116153915214981458040523 28674230872822472187060785)
  ·
    refine ⟨21505673154616854140295589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28674230872822472187060785 21505673154616854140295589)
    ·
      refine ⟨4032313716490660151305423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21505673154616854140295589 4032313716490660151305423)
      ·
        refine ⟨6048470574735990226958135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4032313716490660151305423 6048470574735990226958135)
        ·
          refine ⟨9072705862103985340437203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6048470574735990226958135 9072705862103985340437203)
          ·
            refine ⟨13609058793155978010655805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9072705862103985340437203 13609058793155978010655805)
            ·
              refine ⟨5103397047433491753995927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13609058793155978010655805 5103397047433491753995927)
              ·
                refine ⟨7655095571150237630993891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5103397047433491753995927 7655095571150237630993891)
                ·
                  refine ⟨11482643356725356446490837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7655095571150237630993891 11482643356725356446490837)
                  ·
                    refine ⟨269124453673250541714629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11482643356725356446490837 269124453673250541714629)
                    ·
                      rfl

theorem cell22_786177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_786177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_786177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_786177 prefixEnd_786177 := by exact prefixLift 786177
  have htrace : WordTrace (prefixWord ++ tailWord_786177) baseStart_786177 baseEnd_786177 := by
    simpa [prefixWord, tailWord_786177, baseEnd_786177] using wordTrace_append hprefix tailTrace_786177
  have hstable : (prefixWord ++ tailWord_786177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786177).length < 2 ^ (prefixWord ++ tailWord_786177).sum := by decide
  have hdescent : baseEnd_786177 < baseStart_786177 := by decide
  rcases family_descends (prefixWord ++ tailWord_786177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786207 : List Nat := [1, 1, 2, 4, 2, 1, 1, 2, 8]
def baseStart_786207 : Nat := 118140960795 + 786207 * 2 ^ 59
def prefixEnd_786207 : Nat := 4983230072969 + 3 ^ 40 * 786207 * 2
def baseEnd_786207 : Nat := 89711574428780154488179

theorem tailTrace_786207 : CollatzResearch.WordTrace tailWord_786207 prefixEnd_786207 89711574428780154488179 := by
  unfold tailWord_786207
  simp only [CollatzResearch.WordTrace]
  refine ⟨28675325062713787310652875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19116883375142524873768583 28675325062713787310652875)
  ·
    refine ⟨43012987594070680965979313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28675325062713787310652875 43012987594070680965979313)
    ·
      refine ⟨32259740695553010724484485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43012987594070680965979313 32259740695553010724484485)
      ·
        refine ⟨6048701380416189510840841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32259740695553010724484485 6048701380416189510840841)
        ·
          refine ⟨4536526035312142133130631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6048701380416189510840841 4536526035312142133130631)
          ·
            refine ⟨6804789052968213199695947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4536526035312142133130631 6804789052968213199695947)
            ·
              refine ⟨10207183579452319799543921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6804789052968213199695947 10207183579452319799543921)
              ·
                refine ⟨7655387684589239849657941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10207183579452319799543921 7655387684589239849657941)
                ·
                  refine ⟨89711574428780154488179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7655387684589239849657941 89711574428780154488179)
                  ·
                    rfl

theorem cell22_786207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 8].length) (baseStart_786207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_786207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_786207 prefixEnd_786207 := by exact prefixLift 786207
  have htrace : WordTrace (prefixWord ++ tailWord_786207) baseStart_786207 baseEnd_786207 := by
    simpa [prefixWord, tailWord_786207, baseEnd_786207] using wordTrace_append hprefix tailTrace_786207
  have hstable : (prefixWord ++ tailWord_786207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786207).length < 2 ^ (prefixWord ++ tailWord_786207).sum := by decide
  have hdescent : baseEnd_786207 < baseStart_786207 := by decide
  rcases family_descends (prefixWord ++ tailWord_786207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786258 : List Nat := [3, 2, 2, 1, 1, 5, 1, 3, 4]
def baseStart_786258 : Nat := 118140960795 + 786258 * 2 ^ 59
def prefixEnd_786258 : Nat := 4983230072969 + 3 ^ 40 * 786258 * 2
def baseEnd_786258 : Nat := 89717393876197776813127

theorem tailTrace_786258 : CollatzResearch.WordTrace tailWord_786258 prefixEnd_786258 89717393876197776813127 := by
  unfold tailWord_786258
  simp only [CollatzResearch.WordTrace]
  refine ⟨7169296296382255755189857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19118123457019348680506285 7169296296382255755189857)
  ·
    refine ⟨5376972222286691816392393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7169296296382255755189857 5376972222286691816392393)
    ·
      refine ⟨4032729166715018862294295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5376972222286691816392393 4032729166715018862294295)
      ·
        refine ⟨6049093750072528293441443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4032729166715018862294295 6049093750072528293441443)
        ·
          refine ⟨9073640625108792440162165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6049093750072528293441443 9073640625108792440162165)
          ·
            refine ⟨850653808603949291265203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9073640625108792440162165 850653808603949291265203)
            ·
              refine ⟨1275980712905923936897805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 850653808603949291265203 1275980712905923936897805)
              ·
                refine ⟨478492767339721476336677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1275980712905923936897805 478492767339721476336677)
                ·
                  refine ⟨89717393876197776813127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 478492767339721476336677 89717393876197776813127)
                  ·
                    rfl

theorem cell22_786258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 3, 4].length) (baseStart_786258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_786258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_786258 prefixEnd_786258 := by exact prefixLift 786258
  have htrace : WordTrace (prefixWord ++ tailWord_786258) baseStart_786258 baseEnd_786258 := by
    simpa [prefixWord, tailWord_786258, baseEnd_786258] using wordTrace_append hprefix tailTrace_786258
  have hstable : (prefixWord ++ tailWord_786258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786258).length < 2 ^ (prefixWord ++ tailWord_786258).sum := by decide
  have hdescent : baseEnd_786258 < baseStart_786258 := by decide
  rcases family_descends (prefixWord ++ tailWord_786258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786286 : List Nat := [4, 1, 2, 3, 1, 2, 2, 7]
def baseStart_786286 : Nat := 118140960795 + 786286 * 2 ^ 59
def prefixEnd_786286 : Nat := 4983230072969 + 3 ^ 40 * 786286 * 2
def baseEnd_786286 : Nat := 29906862955645621193255

theorem tailTrace_786286 : CollatzResearch.WordTrace tailWord_786286 prefixEnd_786286 29906862955645621193255 := by
  unfold tailWord_786286
  simp only [CollatzResearch.WordTrace]
  refine ⟨3584775803678447975347339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19118804286285055868519141 3584775803678447975347339)
  ·
    refine ⟨5377163705517671963021009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3584775803678447975347339 5377163705517671963021009)
    ·
      refine ⟨4032872779138253972265757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5377163705517671963021009 4032872779138253972265757)
      ·
        refine ⟨1512327292176845239599659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4032872779138253972265757 1512327292176845239599659)
        ·
          refine ⟨2268490938265267859399489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1512327292176845239599659 2268490938265267859399489)
          ·
            refine ⟨1701368203698950894549617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2268490938265267859399489 1701368203698950894549617)
            ·
              refine ⟨1276026152774213170912213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1701368203698950894549617 1276026152774213170912213)
              ·
                refine ⟨29906862955645621193255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1276026152774213170912213 29906862955645621193255)
                ·
                  rfl

theorem cell22_786286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 7].length) (baseStart_786286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_786286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_786286 prefixEnd_786286 := by exact prefixLift 786286
  have htrace : WordTrace (prefixWord ++ tailWord_786286) baseStart_786286 baseEnd_786286 := by
    simpa [prefixWord, tailWord_786286, baseEnd_786286] using wordTrace_append hprefix tailTrace_786286
  have hstable : (prefixWord ++ tailWord_786286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786286).length < 2 ^ (prefixWord ++ tailWord_786286).sum := by decide
  have hdescent : baseEnd_786286 < baseStart_786286 := by decide
  rcases family_descends (prefixWord ++ tailWord_786286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786326 : List Nat := [5, 3, 1, 1, 3, 1, 2, 2, 4]
def baseStart_786326 : Nat := 118140960795 + 786326 * 2 ^ 59
def prefixEnd_786326 : Nat := 4983230072969 + 3 ^ 40 * 786326 * 2
def baseEnd_786326 : Nat := 89725153139421273246391

theorem tailTrace_786326 : CollatzResearch.WordTrace tailWord_786326 prefixEnd_786326 89725153139421273246391 := by
  unfold tailWord_786326
  simp only [CollatzResearch.WordTrace]
  refine ⟨1792479084330166914639677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19119776899521780422823221 1792479084330166914639677)
  ·
    refine ⟨672179656623812592989879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1792479084330166914639677 672179656623812592989879)
    ·
      refine ⟨1008269484935718889484819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 672179656623812592989879 1008269484935718889484819)
      ·
        refine ⟨1512404227403578334227229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1008269484935718889484819 1512404227403578334227229)
        ·
          refine ⟨567151585276341875335211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1512404227403578334227229 567151585276341875335211)
          ·
            refine ⟨850727377914512813002817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 567151585276341875335211 850727377914512813002817)
            ·
              refine ⟨638045533435884609752113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 850727377914512813002817 638045533435884609752113)
              ·
                refine ⟨478534150076913457314085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 638045533435884609752113 478534150076913457314085)
                ·
                  refine ⟨89725153139421273246391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 478534150076913457314085 89725153139421273246391)
                  ·
                    rfl

theorem cell22_786326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_786326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_786326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_786326 prefixEnd_786326 := by exact prefixLift 786326
  have htrace : WordTrace (prefixWord ++ tailWord_786326) baseStart_786326 baseEnd_786326 := by
    simpa [prefixWord, tailWord_786326, baseEnd_786326] using wordTrace_append hprefix tailTrace_786326
  have hstable : (prefixWord ++ tailWord_786326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786326).length < 2 ^ (prefixWord ++ tailWord_786326).sum := by decide
  have hdescent : baseEnd_786326 < baseStart_786326 := by decide
  rcases family_descends (prefixWord ++ tailWord_786326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786335 : List Nat := [1, 1, 2, 5, 3, 1, 1, 4, 1, 3]
def baseStart_786335 : Nat := 118140960795 + 786335 * 2 ^ 59
def prefixEnd_786335 : Nat := 4983230072969 + 3 ^ 40 * 786335 * 2
def baseEnd_786335 : Nat := 269178540302190796264145

theorem tailTrace_786335 : CollatzResearch.WordTrace tailWord_786335 prefixEnd_786335 269178540302190796264145 := by
  unfold tailWord_786335
  simp only [CollatzResearch.WordTrace]
  refine ⟨28679993606250065171312459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19119995737500043447541639 28679993606250065171312459)
  ·
    refine ⟨43019990409375097756968689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28679993606250065171312459 43019990409375097756968689)
    ·
      refine ⟨32264992807031323317726517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43019990409375097756968689 32264992807031323317726517)
      ·
        refine ⟨3024843075659186561036861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32264992807031323317726517 3024843075659186561036861)
        ·
          refine ⟨1134316153372194960388823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3024843075659186561036861 1134316153372194960388823)
          ·
            refine ⟨1701474230058292440583235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1134316153372194960388823 1701474230058292440583235)
            ·
              refine ⟨2552211345087438660874853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1701474230058292440583235 2552211345087438660874853)
              ·
                refine ⟨478539627203894748914035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2552211345087438660874853 478539627203894748914035)
                ·
                  refine ⟨717809440805842123371053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 478539627203894748914035 717809440805842123371053)
                  ·
                    refine ⟨269178540302190796264145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 717809440805842123371053 269178540302190796264145)
                    ·
                      rfl

theorem cell22_786335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 4, 1, 3].length) (baseStart_786335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_786335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_786335 prefixEnd_786335 := by exact prefixLift 786335
  have htrace : WordTrace (prefixWord ++ tailWord_786335) baseStart_786335 baseEnd_786335 := by
    simpa [prefixWord, tailWord_786335, baseEnd_786335] using wordTrace_append hprefix tailTrace_786335
  have hstable : (prefixWord ++ tailWord_786335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786335).length < 2 ^ (prefixWord ++ tailWord_786335).sum := by decide
  have hdescent : baseEnd_786335 < baseStart_786335 := by decide
  rcases family_descends (prefixWord ++ tailWord_786335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786361 : List Nat := [1, 2, 1, 4, 2, 1, 2, 4, 1, 4]
def baseStart_786361 : Nat := 118140960795 + 786361 * 2 ^ 59
def prefixEnd_786361 : Nat := 4983230072969 + 3 ^ 40 * 786361 * 2
def baseEnd_786361 : Nat := 269187440633535395114065

theorem tailTrace_786361 : CollatzResearch.WordTrace tailWord_786361 prefixEnd_786361 269187440633535395114065 := by
  unfold tailWord_786361
  simp only [CollatzResearch.WordTrace]
  refine ⟨28680941904155871611758937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19120627936103914407839291 28680941904155871611758937)
  ·
    refine ⟨21510706428116903708819203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28680941904155871611758937 21510706428116903708819203)
    ·
      refine ⟨32266059642175355563228805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21510706428116903708819203 32266059642175355563228805)
      ·
        refine ⟨6049886182907879168105401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32266059642175355563228805 6049886182907879168105401)
        ·
          refine ⟨4537414637180909376079051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6049886182907879168105401 4537414637180909376079051)
          ·
            refine ⟨6806121955771364064118577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4537414637180909376079051 6806121955771364064118577)
            ·
              refine ⟨5104591466828523048088933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6806121955771364064118577 5104591466828523048088933)
              ·
                refine ⟨957110900030348071516675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5104591466828523048088933 957110900030348071516675)
                ·
                  refine ⟨1435666350045522107275013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 957110900030348071516675 1435666350045522107275013)
                  ·
                    refine ⟨269187440633535395114065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1435666350045522107275013 269187440633535395114065)
                    ·
                      rfl

theorem cell22_786361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 4, 1, 4].length) (baseStart_786361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_786361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_786361 prefixEnd_786361 := by exact prefixLift 786361
  have htrace : WordTrace (prefixWord ++ tailWord_786361) baseStart_786361 baseEnd_786361 := by
    simpa [prefixWord, tailWord_786361, baseEnd_786361] using wordTrace_append hprefix tailTrace_786361
  have hstable : (prefixWord ++ tailWord_786361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786361).length < 2 ^ (prefixWord ++ tailWord_786361).sum := by decide
  have hdescent : baseEnd_786361 < baseStart_786361 := by decide
  rcases family_descends (prefixWord ++ tailWord_786361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786378 : List Nat := [3, 1, 2, 1, 2, 1, 6, 1, 1, 4]
def baseStart_786378 : Nat := 118140960795 + 786378 * 2 ^ 59
def prefixEnd_786378 : Nat := 4983230072969 + 3 ^ 40 * 786378 * 2
def baseEnd_786378 : Nat := 269193260080953017439013

theorem tailTrace_786378 : CollatzResearch.WordTrace tailWord_786378 prefixEnd_786378 269193260080953017439013 := by
  unfold tailWord_786378
  simp only [CollatzResearch.WordTrace]
  refine ⟨7170390486273570878781947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19121041296729522343418525 7170390486273570878781947)
  ·
    refine ⟨10755585729410356318172921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7170390486273570878781947 10755585729410356318172921)
    ·
      refine ⟨8066689297057767238629691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10755585729410356318172921 8066689297057767238629691)
      ·
        refine ⟨12100033945586650857944537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8066689297057767238629691 12100033945586650857944537)
        ·
          refine ⟨9075025459189988143458403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12100033945586650857944537 9075025459189988143458403)
          ·
            refine ⟨13612538188784982215187605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9075025459189988143458403 13612538188784982215187605)
            ·
              refine ⟨638087727599296041336919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13612538188784982215187605 638087727599296041336919)
              ·
                refine ⟨957131591398944062005379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 638087727599296041336919 957131591398944062005379)
                ·
                  refine ⟨1435697387098416093008069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 957131591398944062005379 1435697387098416093008069)
                  ·
                    refine ⟨269193260080953017439013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1435697387098416093008069 269193260080953017439013)
                    ·
                      rfl

theorem cell22_786378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 1, 1, 4].length) (baseStart_786378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_786378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_786378 prefixEnd_786378 := by exact prefixLift 786378
  have htrace : WordTrace (prefixWord ++ tailWord_786378) baseStart_786378 baseEnd_786378 := by
    simpa [prefixWord, tailWord_786378, baseEnd_786378] using wordTrace_append hprefix tailTrace_786378
  have hstable : (prefixWord ++ tailWord_786378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786378).length < 2 ^ (prefixWord ++ tailWord_786378).sum := by decide
  have hdescent : baseEnd_786378 < baseStart_786378 := by decide
  rcases family_descends (prefixWord ++ tailWord_786378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786391 : List Nat := [1, 1, 3, 2, 1, 1, 5, 1, 4, 3]
def baseStart_786391 : Nat := 118140960795 + 786391 * 2 ^ 59
def prefixEnd_786391 : Nat := 4983230072969 + 3 ^ 40 * 786391 * 2
def baseEnd_786391 : Nat := 269197710246625316863973

theorem tailTrace_786391 : CollatzResearch.WordTrace tailWord_786391 prefixEnd_786391 269197710246625316863973 := by
  unfold tailWord_786391
  simp only [CollatzResearch.WordTrace]
  refine ⟨28682036094047186735351027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19121357396031457823567351 28682036094047186735351027)
  ·
    refine ⟨43023054141070780103026541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28682036094047186735351027 43023054141070780103026541)
    ·
      refine ⟨16133645302901542538634953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43023054141070780103026541 16133645302901542538634953)
      ·
        refine ⟨12100233977176156903976215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16133645302901542538634953 12100233977176156903976215)
        ·
          refine ⟨18150350965764235355964323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12100233977176156903976215 18150350965764235355964323)
          ·
            refine ⟨27225526448646353033946485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18150350965764235355964323 27225526448646353033946485)
            ·
              refine ⟨2552393104560595596932483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27225526448646353033946485 2552393104560595596932483)
              ·
                refine ⟨3828589656840893395398725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2552393104560595596932483 3828589656840893395398725)
                ·
                  refine ⟨717860560657667511637261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3828589656840893395398725 717860560657667511637261)
                  ·
                    refine ⟨269197710246625316863973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 717860560657667511637261 269197710246625316863973)
                    ·
                      rfl

theorem cell22_786391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 4, 3].length) (baseStart_786391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_786391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_786391 prefixEnd_786391 := by exact prefixLift 786391
  have htrace : WordTrace (prefixWord ++ tailWord_786391) baseStart_786391 baseEnd_786391 := by
    simpa [prefixWord, tailWord_786391, baseEnd_786391] using wordTrace_append hprefix tailTrace_786391
  have hstable : (prefixWord ++ tailWord_786391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786391).length < 2 ^ (prefixWord ++ tailWord_786391).sum := by decide
  have hdescent : baseEnd_786391 < baseStart_786391 := by decide
  rcases family_descends (prefixWord ++ tailWord_786391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786404 : List Nat := [2, 3, 1, 1, 1, 1, 4, 9]
def baseStart_786404 : Nat := 118140960795 + 786404 * 2 ^ 59
def prefixEnd_786404 : Nat := 4983230072969 + 3 ^ 40 * 786404 * 2
def baseEnd_786404 : Nat := 29911351156921957365437

theorem tailTrace_786404 : CollatzResearch.WordTrace tailWord_786404 prefixEnd_786404 29911351156921957365437 := by
  unfold tailWord_786404
  simp only [CollatzResearch.WordTrace]
  refine ⟨14341255121500044977787133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19121673495333393303716177 14341255121500044977787133)
  ·
    refine ⟨5377970670562516866670175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14341255121500044977787133 5377970670562516866670175)
    ·
      refine ⟨8066956005843775300005263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5377970670562516866670175 8066956005843775300005263)
      ·
        refine ⟨12100434008765662950007895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8066956005843775300005263 12100434008765662950007895)
        ·
          refine ⟨18150651013148494425011843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12100434008765662950007895 18150651013148494425011843)
          ·
            refine ⟨27225976519722741637517765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18150651013148494425011843 27225976519722741637517765)
            ·
              refine ⟨5104870597448014057034581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27225976519722741637517765 5104870597448014057034581)
              ·
                refine ⟨29911351156921957365437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5104870597448014057034581 29911351156921957365437)
                ·
                  rfl

theorem cell22_786404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 9].length) (baseStart_786404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_786404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_786404 prefixEnd_786404 := by exact prefixLift 786404
  have htrace : WordTrace (prefixWord ++ tailWord_786404) baseStart_786404 baseEnd_786404 := by
    simpa [prefixWord, tailWord_786404, baseEnd_786404] using wordTrace_append hprefix tailTrace_786404
  have hstable : (prefixWord ++ tailWord_786404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786404).length < 2 ^ (prefixWord ++ tailWord_786404).sum := by decide
  have hdescent : baseEnd_786404 < baseStart_786404 := by decide
  rcases family_descends (prefixWord ++ tailWord_786404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786556 : List Nat := [2, 2, 2, 1, 1, 5, 9]
def baseStart_786556 : Nat := 118140960795 + 786556 * 2 ^ 59
def prefixEnd_786556 : Nat := 4983230072969 + 3 ^ 40 * 786556 * 2
def baseEnd_786556 : Nat := 9972377522911847647721

theorem tailTrace_786556 : CollatzResearch.WordTrace tailWord_786556 prefixEnd_786556 9972377522911847647721 := by
  unfold tailWord_786556
  simp only [CollatzResearch.WordTrace]
  refine ⟨14344027069224709957553761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19125369425632946610071681 14344027069224709957553761)
  ·
    refine ⟨10758020301918532468165321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14344027069224709957553761 10758020301918532468165321)
    ·
      refine ⟨8068515226438899351123991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10758020301918532468165321 8068515226438899351123991)
      ·
        refine ⟨12102772839658349026685987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8068515226438899351123991 12102772839658349026685987)
        ·
          refine ⟨18154159259487523540028981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12102772839658349026685987 18154159259487523540028981)
          ·
            refine ⟨1701952430576955331877717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18154159259487523540028981 1701952430576955331877717)
            ·
              refine ⟨9972377522911847647721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1701952430576955331877717 9972377522911847647721)
              ·
                rfl

theorem cell22_786556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 9].length) (baseStart_786556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_786556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_786556 prefixEnd_786556 := by exact prefixLift 786556
  have htrace : WordTrace (prefixWord ++ tailWord_786556) baseStart_786556 baseEnd_786556 := by
    simpa [prefixWord, tailWord_786556, baseEnd_786556] using wordTrace_append hprefix tailTrace_786556
  have hstable : (prefixWord ++ tailWord_786556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786556).length < 2 ^ (prefixWord ++ tailWord_786556).sum := by decide
  have hdescent : baseEnd_786556 < baseStart_786556 := by decide
  rcases family_descends (prefixWord ++ tailWord_786556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786590 : List Nat := [4, 3, 1, 1, 3, 1, 1, 8]
def baseStart_786590 : Nat := 118140960795 + 786590 * 2 ^ 59
def prefixEnd_786590 : Nat := 4983230072969 + 3 ^ 40 * 786590 * 2
def baseEnd_786590 : Nat := 29918425779272792348707

theorem tailTrace_786590 : CollatzResearch.WordTrace tailWord_786590 prefixEnd_786590 29918425779272792348707 := by
  unfold tailWord_786590
  simp only [CollatzResearch.WordTrace]
  refine ⟨3586161777540780465230653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19126196146884162481230149 3586161777540780465230653)
  ·
    refine ⟨1344810666577792674461495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3586161777540780465230653 1344810666577792674461495)
    ·
      refine ⟨2017215999866689011692243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1344810666577792674461495 2017215999866689011692243)
      ·
        refine ⟨3025823999800033517538365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2017215999866689011692243 3025823999800033517538365)
        ·
          refine ⟨1134683999925012569076887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3025823999800033517538365 1134683999925012569076887)
          ·
            refine ⟨1702025999887518853615331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1134683999925012569076887 1702025999887518853615331)
            ·
              refine ⟨2553038999831278280422997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1702025999887518853615331 2553038999831278280422997)
              ·
                refine ⟨29918425779272792348707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2553038999831278280422997 29918425779272792348707)
                ·
                  rfl

theorem cell22_786590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 8].length) (baseStart_786590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_786590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_786590 prefixEnd_786590 := by exact prefixLift 786590
  have htrace : WordTrace (prefixWord ++ tailWord_786590) baseStart_786590 baseEnd_786590 := by
    simpa [prefixWord, tailWord_786590, baseEnd_786590] using wordTrace_append hprefix tailTrace_786590
  have hstable : (prefixWord ++ tailWord_786590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786590).length < 2 ^ (prefixWord ++ tailWord_786590).sum := by decide
  have hdescent : baseEnd_786590 < baseStart_786590 := by decide
  rcases family_descends (prefixWord ++ tailWord_786590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786631 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 1, 10]
def baseStart_786631 : Nat := 118140960795 + 786631 * 2 ^ 59
def prefixEnd_786631 : Nat := 4983230072969 + 3 ^ 40 * 786631 * 2
def baseEnd_786631 : Nat := 269279867151344690863237

theorem tailTrace_786631 : CollatzResearch.WordTrace tailWord_786631 prefixEnd_786631 269279867151344690863237 := by
  unfold tailWord_786631
  simp only [CollatzResearch.WordTrace]
  refine ⟨28690789613177707724087747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19127193075451805149391831 28690789613177707724087747)
  ·
    refine ⟨43036184419766561586131621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28690789613177707724087747 43036184419766561586131621)
    ·
      refine ⟨8069284578706230297399679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43036184419766561586131621 8069284578706230297399679)
      ·
        refine ⟨12103926868059345446099519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8069284578706230297399679 12103926868059345446099519)
        ·
          refine ⟨18155890302089018169149279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12103926868059345446099519 18155890302089018169149279)
          ·
            refine ⟨27233835453133527253723919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18155890302089018169149279 27233835453133527253723919)
            ·
              refine ⟨40850753179700290880585879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27233835453133527253723919 40850753179700290880585879)
              ·
                refine ⟨61276129769550436320878819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40850753179700290880585879 61276129769550436320878819)
                ·
                  refine ⟨91914194654325654481318229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61276129769550436320878819 91914194654325654481318229)
                  ·
                    refine ⟨269279867151344690863237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 91914194654325654481318229 269279867151344690863237)
                    ·
                      rfl

theorem cell22_786631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_786631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_786631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_786631 prefixEnd_786631 := by exact prefixLift 786631
  have htrace : WordTrace (prefixWord ++ tailWord_786631) baseStart_786631 baseEnd_786631 := by
    simpa [prefixWord, tailWord_786631, baseEnd_786631] using wordTrace_append hprefix tailTrace_786631
  have hstable : (prefixWord ++ tailWord_786631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786631).length < 2 ^ (prefixWord ++ tailWord_786631).sum := by decide
  have hdescent : baseEnd_786631 < baseStart_786631 := by decide
  rcases family_descends (prefixWord ++ tailWord_786631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786791 : List Nat := [1, 1, 5, 1, 3, 2, 3, 2, 1, 3]
def baseStart_786791 : Nat := 118140960795 + 786791 * 2 ^ 59
def prefixEnd_786791 : Nat := 4983230072969 + 3 ^ 40 * 786791 * 2
def baseEnd_786791 : Nat := 269334638421157606862747

theorem tailTrace_786791 : CollatzResearch.WordTrace tailWord_786791 prefixEnd_786791 269334638421157606862747 := by
  unfold tailWord_786791
  simp only [CollatzResearch.WordTrace]
  refine ⟨28696625292598055049912227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19131083528398703366608151 28696625292598055049912227)
  ·
    refine ⟨43044937938897082574868341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28696625292598055049912227 43044937938897082574868341)
    ·
      refine ⟨4035462931771601491393907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43044937938897082574868341 4035462931771601491393907)
      ·
        refine ⟨6053194397657402237090861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4035462931771601491393907 6053194397657402237090861)
        ·
          refine ⟨2269947899121525838909073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6053194397657402237090861 2269947899121525838909073)
          ·
            refine ⟨1702460924341144379181805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2269947899121525838909073 1702460924341144379181805)
            ·
              refine ⟨638422846627929142193177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1702460924341144379181805 638422846627929142193177)
              ·
                refine ⟨478817134970946856644883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 638422846627929142193177 478817134970946856644883)
                ·
                  refine ⟨718225702456420284967325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 478817134970946856644883 718225702456420284967325)
                  ·
                    refine ⟨269334638421157606862747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 718225702456420284967325 269334638421157606862747)
                    ·
                      rfl

theorem cell22_786791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_786791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_786791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_786791 prefixEnd_786791 := by exact prefixLift 786791
  have htrace : WordTrace (prefixWord ++ tailWord_786791) baseStart_786791 baseEnd_786791 := by
    simpa [prefixWord, tailWord_786791, baseEnd_786791] using wordTrace_append hprefix tailTrace_786791
  have hstable : (prefixWord ++ tailWord_786791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786791).length < 2 ^ (prefixWord ++ tailWord_786791).sum := by decide
  have hdescent : baseEnd_786791 < baseStart_786791 := by decide
  rcases family_descends (prefixWord ++ tailWord_786791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786817 : List Nat := [1, 2, 4, 3, 1, 2, 1, 1, 3, 4]
def baseStart_786817 : Nat := 118140960795 + 786817 * 2 ^ 59
def prefixEnd_786817 : Nat := 4983230072969 + 3 ^ 40 * 786817 * 2
def baseEnd_786817 : Nat := 269343538752502205712667

theorem tailTrace_786817 : CollatzResearch.WordTrace tailWord_786817 prefixEnd_786817 269343538752502205712667 := by
  unfold tailWord_786817
  simp only [CollatzResearch.WordTrace]
  refine ⟨28697573590503861490358705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19131715727002574326905803 28697573590503861490358705)
  ·
    refine ⟨21523180192877896117769029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28697573590503861490358705 21523180192877896117769029)
    ·
      refine ⟨4035596286164605522081693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21523180192877896117769029 4035596286164605522081693)
      ·
        refine ⟨1513348607311727070780635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4035596286164605522081693 1513348607311727070780635)
        ·
          refine ⟨2270022910967590606170953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1513348607311727070780635 2270022910967590606170953)
          ·
            refine ⟨1702517183225692954628215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2270022910967590606170953 1702517183225692954628215)
            ·
              refine ⟨2553775774838539431942323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1702517183225692954628215 2553775774838539431942323)
              ·
                refine ⟨3830663662257809147913485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2553775774838539431942323 3830663662257809147913485)
                ·
                  refine ⟨1436498873346678430467557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3830663662257809147913485 1436498873346678430467557)
                  ·
                    refine ⟨269343538752502205712667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1436498873346678430467557 269343538752502205712667)
                    ·
                      rfl

theorem cell22_786817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_786817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_786817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_786817 prefixEnd_786817 := by exact prefixLift 786817
  have htrace : WordTrace (prefixWord ++ tailWord_786817) baseStart_786817 baseEnd_786817 := by
    simpa [prefixWord, tailWord_786817, baseEnd_786817] using wordTrace_append hprefix tailTrace_786817
  have hstable : (prefixWord ++ tailWord_786817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786817).length < 2 ^ (prefixWord ++ tailWord_786817).sum := by decide
  have hdescent : baseEnd_786817 < baseStart_786817 := by decide
  rcases family_descends (prefixWord ++ tailWord_786817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786838 : List Nat := [5, 3, 1, 2, 1, 1, 2, 2, 5]
def baseStart_786838 : Nat := 118140960795 + 786838 * 2 ^ 59
def prefixEnd_786838 : Nat := 4983230072969 + 3 ^ 40 * 786838 * 2
def baseEnd_786838 : Nat := 89783575827221716979201

theorem tailTrace_786838 : CollatzResearch.WordTrace tailWord_786838 prefixEnd_786838 89783575827221716979201 := by
  unfold tailWord_786838
  simp only [CollatzResearch.WordTrace]
  refine ⟨1793646220214236379804573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19132226348951854717915445 1793646220214236379804573)
  ·
    refine ⟨672617332580338642426715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1793646220214236379804573 672617332580338642426715)
    ·
      refine ⟨1008925998870507963640073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 672617332580338642426715 1008925998870507963640073)
      ·
        refine ⟨756694499152880972730055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1008925998870507963640073 756694499152880972730055)
        ·
          refine ⟨1135041748729321459095083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 756694499152880972730055 1135041748729321459095083)
          ·
            refine ⟨1702562623093982188642625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1135041748729321459095083 1702562623093982188642625)
            ·
              refine ⟨1276921967320486641481969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1702562623093982188642625 1276921967320486641481969)
              ·
                refine ⟨957691475490364981111477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1276921967320486641481969 957691475490364981111477)
                ·
                  refine ⟨89783575827221716979201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 957691475490364981111477 89783575827221716979201)
                  ·
                    rfl

theorem cell22_786838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_786838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_786838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_786838 prefixEnd_786838 := by exact prefixLift 786838
  have htrace : WordTrace (prefixWord ++ tailWord_786838) baseStart_786838 baseEnd_786838 := by
    simpa [prefixWord, tailWord_786838, baseEnd_786838] using wordTrace_append hprefix tailTrace_786838
  have hstable : (prefixWord ++ tailWord_786838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786838).length < 2 ^ (prefixWord ++ tailWord_786838).sum := by decide
  have hdescent : baseEnd_786838 < baseStart_786838 := by decide
  rcases family_descends (prefixWord ++ tailWord_786838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786877 : List Nat := [1, 4, 1, 2, 2, 3, 3, 6]
def baseStart_786877 : Nat := 118140960795 + 786877 * 2 ^ 59
def prefixEnd_786877 : Nat := 4983230072969 + 3 ^ 40 * 786877 * 2
def baseEnd_786877 : Nat := 29929341997631338801387

theorem tailTrace_786877 : CollatzResearch.WordTrace tailWord_786877 prefixEnd_786877 29929341997631338801387 := by
  unfold tailWord_786877
  simp only [CollatzResearch.WordTrace]
  refine ⟨28699761970286491737542885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19133174646857661158361923 28699761970286491737542885)
  ·
    refine ⟨5381205369428717200789291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28699761970286491737542885 5381205369428717200789291)
    ·
      refine ⟨8071808054143075801183937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5381205369428717200789291 8071808054143075801183937)
      ·
        refine ⟨6053856040607306850887953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8071808054143075801183937 6053856040607306850887953)
        ·
          refine ⟨4540392030455480138165965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6053856040607306850887953 4540392030455480138165965)
          ·
            refine ⟨1702647011420805051812237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4540392030455480138165965 1702647011420805051812237)
            ·
              refine ⟨638492629282801894429589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1702647011420805051812237 638492629282801894429589)
              ·
                refine ⟨29929341997631338801387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 638492629282801894429589 29929341997631338801387)
                ·
                  rfl

theorem cell22_786877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 6].length) (baseStart_786877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_786877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_786877 prefixEnd_786877 := by exact prefixLift 786877
  have htrace : WordTrace (prefixWord ++ tailWord_786877) baseStart_786877 baseEnd_786877 := by
    simpa [prefixWord, tailWord_786877, baseEnd_786877] using wordTrace_append hprefix tailTrace_786877
  have hstable : (prefixWord ++ tailWord_786877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786877).length < 2 ^ (prefixWord ++ tailWord_786877).sum := by decide
  have hdescent : baseEnd_786877 < baseStart_786877 := by decide
  rcases family_descends (prefixWord ++ tailWord_786877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786898 : List Nat := [3, 2, 2, 4, 1, 2, 1, 2, 2, 3]
def baseStart_786898 : Nat := 118140960795 + 786898 * 2 ^ 59
def prefixEnd_786898 : Nat := 4983230072969 + 3 ^ 40 * 786898 * 2
def baseEnd_786898 : Nat := 269371266707844994437419

theorem tailTrace_786898 : CollatzResearch.WordTrace tailWord_786898 prefixEnd_786898 269371266707844994437419 := by
  unfold tailWord_786898
  simp only [CollatzResearch.WordTrace]
  refine ⟨7175131975802603081014337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19133685268806941549371565 7175131975802603081014337)
  ·
    refine ⟨5381348981851952310760753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7175131975802603081014337 5381348981851952310760753)
    ·
      refine ⟨4036011736388964233070565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5381348981851952310760753 4036011736388964233070565)
      ·
        refine ⟨756752200572930793700731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4036011736388964233070565 756752200572930793700731)
        ·
          refine ⟨1135128300859396190551097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 756752200572930793700731 1135128300859396190551097)
          ·
            refine ⟨851346225644547142913323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1135128300859396190551097 851346225644547142913323)
            ·
              refine ⟨1277019338466820714369985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 851346225644547142913323 1277019338466820714369985)
              ·
                refine ⟨957764503850115535777489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1277019338466820714369985 957764503850115535777489)
                ·
                  refine ⟨718323377887586651833117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 957764503850115535777489 718323377887586651833117)
                  ·
                    refine ⟨269371266707844994437419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 718323377887586651833117 269371266707844994437419)
                    ·
                      rfl

theorem cell22_786898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_786898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_786898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_786898 prefixEnd_786898 := by exact prefixLift 786898
  have htrace : WordTrace (prefixWord ++ tailWord_786898) baseStart_786898 baseEnd_786898 := by
    simpa [prefixWord, tailWord_786898, baseEnd_786898] using wordTrace_append hprefix tailTrace_786898
  have hstable : (prefixWord ++ tailWord_786898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786898).length < 2 ^ (prefixWord ++ tailWord_786898).sum := by decide
  have hdescent : baseEnd_786898 < baseStart_786898 := by decide
  rcases family_descends (prefixWord ++ tailWord_786898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786905 : List Nat := [1, 2, 1, 2, 4, 1, 3, 1, 7]
def baseStart_786905 : Nat := 118140960795 + 786905 * 2 ^ 59
def prefixEnd_786905 : Nat := 4983230072969 + 3 ^ 40 * 786905 * 2
def baseEnd_786905 : Nat := 89791220983633103170799

theorem tailTrace_786905 : CollatzResearch.WordTrace tailWord_786905 prefixEnd_786905 89791220983633103170799 := by
  unfold tailWord_786905
  simp only [CollatzResearch.WordTrace]
  refine ⟨28700783214185052519562169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19133855476123368346374779 28700783214185052519562169)
  ·
    refine ⟨21525587410638789389671627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28700783214185052519562169 21525587410638789389671627)
    ·
      refine ⟨32288381115958184084507441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21525587410638789389671627 32288381115958184084507441)
      ·
        refine ⟨24216285836968638063380581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32288381115958184084507441 24216285836968638063380581)
        ·
          refine ⟨4540553594431619636883859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24216285836968638063380581 4540553594431619636883859)
          ·
            refine ⟨6810830391647429455325789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4540553594431619636883859 6810830391647429455325789)
            ·
              refine ⟨2554061396867786045747171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6810830391647429455325789 2554061396867786045747171)
              ·
                refine ⟨3831092095301679068620757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2554061396867786045747171 3831092095301679068620757)
                ·
                  refine ⟨89791220983633103170799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3831092095301679068620757 89791220983633103170799)
                  ·
                    rfl

theorem cell22_786905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 7].length) (baseStart_786905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_786905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_786905 prefixEnd_786905 := by exact prefixLift 786905
  have htrace : WordTrace (prefixWord ++ tailWord_786905) baseStart_786905 baseEnd_786905 := by
    simpa [prefixWord, tailWord_786905, baseEnd_786905] using wordTrace_append hprefix tailTrace_786905
  have hstable : (prefixWord ++ tailWord_786905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786905).length < 2 ^ (prefixWord ++ tailWord_786905).sum := by decide
  have hdescent : baseEnd_786905 < baseStart_786905 := by decide
  rcases family_descends (prefixWord ++ tailWord_786905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786909 : List Nat := [1, 4, 3, 1, 1, 1, 4, 1, 3, 3]
def baseStart_786909 : Nat := 118140960795 + 786909 * 2 ^ 59
def prefixEnd_786909 : Nat := 4983230072969 + 3 ^ 40 * 786909 * 2
def baseEnd_786909 : Nat := 269375032232644632412385

theorem tailTrace_786909 : CollatzResearch.WordTrace tailWord_786909 prefixEnd_786909 269375032232644632412385 := by
  unfold tailWord_786909
  simp only [CollatzResearch.WordTrace]
  refine ⟨28700929106170561202707781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19133952737447040801805187 28700929106170561202707781)
  ·
    refine ⟨5381424207406980225507709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28700929106170561202707781 5381424207406980225507709)
    ·
      refine ⟨2018034077777617584565391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5381424207406980225507709 2018034077777617584565391)
      ·
        refine ⟨3027051116666426376848087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2018034077777617584565391 3027051116666426376848087)
        ·
          refine ⟨4540576674999639565272131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3027051116666426376848087 4540576674999639565272131)
          ·
            refine ⟨6810865012499459347908197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4540576674999639565272131 6810865012499459347908197)
            ·
              refine ⟨1277037189843648627732787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6810865012499459347908197 1277037189843648627732787)
              ·
                refine ⟨1915555784765472941599181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1277037189843648627732787 1915555784765472941599181)
                ·
                  refine ⟨718333419287052353099693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1915555784765472941599181 718333419287052353099693)
                  ·
                    refine ⟨269375032232644632412385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 718333419287052353099693 269375032232644632412385)
                    ·
                      rfl

theorem cell22_786909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_786909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_786909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_786909 prefixEnd_786909 := by exact prefixLift 786909
  have htrace : WordTrace (prefixWord ++ tailWord_786909) baseStart_786909 baseEnd_786909 := by
    simpa [prefixWord, tailWord_786909, baseEnd_786909] using wordTrace_append hprefix tailTrace_786909
  have hstable : (prefixWord ++ tailWord_786909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786909).length < 2 ^ (prefixWord ++ tailWord_786909).sum := by decide
  have hdescent : baseEnd_786909 < baseStart_786909 := by decide
  rcases family_descends (prefixWord ++ tailWord_786909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786935 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 7, 4]
def baseStart_786935 : Nat := 118140960795 + 786935 * 2 ^ 59
def prefixEnd_786935 : Nat := 4983230072969 + 3 ^ 40 * 786935 * 2
def baseEnd_786935 : Nat := 269383932563989231262305

theorem tailTrace_786935 : CollatzResearch.WordTrace tailWord_786935 prefixEnd_786935 269383932563989231262305 := by
  unfold tailWord_786935
  simp only [CollatzResearch.WordTrace]
  refine ⟨28701877404076367643154259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19134584936050911762102839 28701877404076367643154259)
  ·
    refine ⟨43052816106114551464731389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28701877404076367643154259 43052816106114551464731389)
    ·
      refine ⟨16144806039792956799274271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43052816106114551464731389 16144806039792956799274271)
      ·
        refine ⟨24217209059689435198911407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16144806039792956799274271 24217209059689435198911407)
        ·
          refine ⟨36325813589534152798367111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24217209059689435198911407 36325813589534152798367111)
          ·
            refine ⟨54488720384301229197550667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36325813589534152798367111 54488720384301229197550667)
            ·
              refine ⟨81733080576451843796326001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54488720384301229197550667 81733080576451843796326001)
              ·
                refine ⟨61299810432338882847244501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81733080576451843796326001 61299810432338882847244501)
                ·
                  refine ⟨1436714307007942566732293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 61299810432338882847244501 1436714307007942566732293)
                  ·
                    refine ⟨269383932563989231262305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1436714307007942566732293 269383932563989231262305)
                    ·
                      rfl

theorem cell22_786935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 7, 4].length) (baseStart_786935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_786935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_786935 prefixEnd_786935 := by exact prefixLift 786935
  have htrace : WordTrace (prefixWord ++ tailWord_786935) baseStart_786935 baseEnd_786935 := by
    simpa [prefixWord, tailWord_786935, baseEnd_786935] using wordTrace_append hprefix tailTrace_786935
  have hstable : (prefixWord ++ tailWord_786935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786935).length < 2 ^ (prefixWord ++ tailWord_786935).sum := by decide
  have hdescent : baseEnd_786935 < baseStart_786935 := by decide
  rcases family_descends (prefixWord ++ tailWord_786935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786986 : List Nat := [3, 1, 4, 1, 1, 4, 1, 2, 1, 4]
def baseStart_786986 : Nat := 118140960795 + 786986 * 2 ^ 59
def prefixEnd_786986 : Nat := 4983230072969 + 3 ^ 40 * 786986 * 2
def baseEnd_786986 : Nat := 269401390906242098237149

theorem tailTrace_786986 : CollatzResearch.WordTrace tailWord_786986 prefixEnd_786986 269401390906242098237149 := by
  unfold tailWord_786986
  simp only [CollatzResearch.WordTrace]
  refine ⟨7175934381722900838315203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19135825017927735568840541 7175934381722900838315203)
  ·
    refine ⟨10763901572584351257472805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7175934381722900838315203 10763901572584351257472805)
    ·
      refine ⟨2018231544859565860776151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10763901572584351257472805 2018231544859565860776151)
      ·
        refine ⟨3027347317289348791164227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2018231544859565860776151 3027347317289348791164227)
        ·
          refine ⟨4541020975934023186746341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3027347317289348791164227 4541020975934023186746341)
          ·
            refine ⟨851441432987629347514939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4541020975934023186746341 851441432987629347514939)
            ·
              refine ⟨1277162149481444021272409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 851441432987629347514939 1277162149481444021272409)
              ·
                refine ⟨957871612111083015954307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1277162149481444021272409 957871612111083015954307)
                ·
                  refine ⟨1436807418166624523931461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 957871612111083015954307 1436807418166624523931461)
                  ·
                    refine ⟨269401390906242098237149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1436807418166624523931461 269401390906242098237149)
                    ·
                      rfl

theorem cell22_786986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_786986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_786986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_786986 prefixEnd_786986 := by exact prefixLift 786986
  have htrace : WordTrace (prefixWord ++ tailWord_786986) baseStart_786986 baseEnd_786986 := by
    simpa [prefixWord, tailWord_786986, baseEnd_786986] using wordTrace_append hprefix tailTrace_786986
  have hstable : (prefixWord ++ tailWord_786986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786986).length < 2 ^ (prefixWord ++ tailWord_786986).sum := by decide
  have hdescent : baseEnd_786986 < baseStart_786986 := by decide
  rcases family_descends (prefixWord ++ tailWord_786986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786995 : List Nat := [1, 1, 1, 2, 4, 2, 1, 10]
def baseStart_786995 : Nat := 118140960795 + 786995 * 2 ^ 59
def prefixEnd_786995 : Nat := 4983230072969 + 3 ^ 40 * 786995 * 2
def baseEnd_786995 : Nat := 29933830198907674973569

theorem tailTrace_786995 : CollatzResearch.WordTrace tailWord_786995 prefixEnd_786995 29933830198907674973569 := by
  unfold tailWord_786995
  simp only [CollatzResearch.WordTrace]
  refine ⟨28704065783858997890338439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19136043855905998593558959 28704065783858997890338439)
  ·
    refine ⟨43056098675788496835507659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28704065783858997890338439 43056098675788496835507659)
    ·
      refine ⟨64584148013682745253261489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43056098675788496835507659 64584148013682745253261489)
      ·
        refine ⟨48438111010262058939946117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64584148013682745253261489 48438111010262058939946117)
        ·
          refine ⟨9082145814424136051239897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48438111010262058939946117 9082145814424136051239897)
          ·
            refine ⟨6811609360818102038429923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9082145814424136051239897 6811609360818102038429923)
            ·
              refine ⟨10217414041227153057644885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6811609360818102038429923 10217414041227153057644885)
              ·
                refine ⟨29933830198907674973569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 10217414041227153057644885 29933830198907674973569)
                ·
                  rfl

theorem cell22_786995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 10].length) (baseStart_786995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_786995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_786995 prefixEnd_786995 := by exact prefixLift 786995
  have htrace : WordTrace (prefixWord ++ tailWord_786995) baseStart_786995 baseEnd_786995 := by
    simpa [prefixWord, tailWord_786995, baseEnd_786995] using wordTrace_append hprefix tailTrace_786995
  have hstable : (prefixWord ++ tailWord_786995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786995).length < 2 ^ (prefixWord ++ tailWord_786995).sum := by decide
  have hdescent : baseEnd_786995 < baseStart_786995 := by decide
  rcases family_descends (prefixWord ++ tailWord_786995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787044 : List Nat := [2, 3, 1, 1, 2, 2, 3, 2, 3, 3]
def baseStart_787044 : Nat := 118140960795 + 787044 * 2 ^ 59
def prefixEnd_787044 : Nat := 4983230072969 + 3 ^ 40 * 787044 * 2
def baseEnd_787044 : Nat := 269421245491549280286971

theorem tailTrace_787044 : CollatzResearch.WordTrace tailWord_787044 prefixEnd_787044 269421245491549280286971 := by
  unfold tailWord_787044
  simp only [CollatzResearch.WordTrace]
  refine ⟨14352926480340739629436093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19137235307120986172581457 14352926480340739629436093)
  ·
    refine ⟨5382347430127777361038535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14352926480340739629436093 5382347430127777361038535)
    ·
      refine ⟨8073521145191666041557803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5382347430127777361038535 8073521145191666041557803)
      ·
        refine ⟨12110281717787499062336705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8073521145191666041557803 12110281717787499062336705)
        ·
          refine ⟨9082711288340624296752529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12110281717787499062336705 9082711288340624296752529)
          ·
            refine ⟨6812033466255468222564397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9082711288340624296752529 6812033466255468222564397)
            ·
              refine ⟨2554512549845800583461649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6812033466255468222564397 2554512549845800583461649)
              ·
                refine ⟨1915884412384350437596237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2554512549845800583461649 1915884412384350437596237)
                ·
                  refine ⟨718456654644131414098589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1915884412384350437596237 718456654644131414098589)
                  ·
                    refine ⟨269421245491549280286971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 718456654644131414098589 269421245491549280286971)
                    ·
                      rfl

theorem cell22_787044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 3, 3].length) (baseStart_787044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_787044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_787044 prefixEnd_787044 := by exact prefixLift 787044
  have htrace : WordTrace (prefixWord ++ tailWord_787044) baseStart_787044 baseEnd_787044 := by
    simpa [prefixWord, tailWord_787044, baseEnd_787044] using wordTrace_append hprefix tailTrace_787044
  have hstable : (prefixWord ++ tailWord_787044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787044).length < 2 ^ (prefixWord ++ tailWord_787044).sum := by decide
  have hdescent : baseEnd_787044 < baseStart_787044 := by decide
  rcases family_descends (prefixWord ++ tailWord_787044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787048 : List Nat := [2, 1, 4, 3, 3, 1, 1, 1, 2, 4]
def baseStart_787048 : Nat := 118140960795 + 787048 * 2 ^ 59
def prefixEnd_787048 : Nat := 4983230072969 + 3 ^ 40 * 787048 * 2
def baseEnd_787048 : Nat := 269422614773294603186959

theorem tailTrace_787048 : CollatzResearch.WordTrace tailWord_787048 prefixEnd_787048 269422614773294603186959 := by
  unfold tailWord_787048
  simp only [CollatzResearch.WordTrace]
  refine ⟨14352999426333493971008899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19137332568444658628011865 14352999426333493971008899)
  ·
    refine ⟨21529499139500240956513349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14352999426333493971008899 21529499139500240956513349)
    ·
      refine ⟨4036781088656295179346253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21529499139500240956513349 4036781088656295179346253)
      ·
        refine ⟨1513792908246110692254845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4036781088656295179346253 1513792908246110692254845)
        ·
          refine ⟨567672340592291509595567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1513792908246110692254845 567672340592291509595567)
          ·
            refine ⟨851508510888437264393351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 567672340592291509595567 851508510888437264393351)
            ·
              refine ⟨1277262766332655896590027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 851508510888437264393351 1277262766332655896590027)
              ·
                refine ⟨1915894149498983844885041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1277262766332655896590027 1915894149498983844885041)
                ·
                  refine ⟨1436920612124237883663781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1915894149498983844885041 1436920612124237883663781)
                  ·
                    refine ⟨269422614773294603186959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1436920612124237883663781 269422614773294603186959)
                    ·
                      rfl

theorem cell22_787048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_787048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_787048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_787048 prefixEnd_787048 := by exact prefixLift 787048
  have htrace : WordTrace (prefixWord ++ tailWord_787048) baseStart_787048 baseEnd_787048 := by
    simpa [prefixWord, tailWord_787048, baseEnd_787048] using wordTrace_append hprefix tailTrace_787048
  have hstable : (prefixWord ++ tailWord_787048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787048).length < 2 ^ (prefixWord ++ tailWord_787048).sum := by decide
  have hdescent : baseEnd_787048 < baseStart_787048 := by decide
  rcases family_descends (prefixWord ++ tailWord_787048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787072 : List Nat := [2, 1, 1, 2, 1, 5, 1, 2, 2, 5]
def baseStart_787072 : Nat := 118140960795 + 787072 * 2 ^ 59
def prefixEnd_787072 : Nat := 4983230072969 + 3 ^ 40 * 787072 * 2
def baseEnd_787072 : Nat := 269430830463766540586885

theorem tailTrace_787072 : CollatzResearch.WordTrace tailWord_787072 prefixEnd_787072 269430830463766540586885 := by
  unfold tailWord_787072
  simp only [CollatzResearch.WordTrace]
  refine ⟨14353437102290020020445735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19137916136386693360594313 14353437102290020020445735)
  ·
    refine ⟨21530155653435030030668603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14353437102290020020445735 21530155653435030030668603)
    ·
      refine ⟨32295233480152545046002905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21530155653435030030668603 32295233480152545046002905)
      ·
        refine ⟨24221425110114408784502179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32295233480152545046002905 24221425110114408784502179)
        ·
          refine ⟨36332137665171613176753269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24221425110114408784502179 36332137665171613176753269)
          ·
            refine ⟨3406137906109838735320619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36332137665171613176753269 3406137906109838735320619)
            ·
              refine ⟨5109206859164758102980929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3406137906109838735320619 5109206859164758102980929)
              ·
                refine ⟨3831905144373568577235697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5109206859164758102980929 3831905144373568577235697)
                ·
                  refine ⟨2873928858280176432926773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3831905144373568577235697 2873928858280176432926773)
                  ·
                    refine ⟨269430830463766540586885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2873928858280176432926773 269430830463766540586885)
                    ·
                      rfl

theorem cell22_787072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 2, 5].length) (baseStart_787072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_787072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_787072 prefixEnd_787072 := by exact prefixLift 787072
  have htrace : WordTrace (prefixWord ++ tailWord_787072) baseStart_787072 baseEnd_787072 := by
    simpa [prefixWord, tailWord_787072, baseEnd_787072] using wordTrace_append hprefix tailTrace_787072
  have hstable : (prefixWord ++ tailWord_787072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787072).length < 2 ^ (prefixWord ++ tailWord_787072).sum := by decide
  have hdescent : baseEnd_787072 < baseStart_787072 := by decide
  rcases family_descends (prefixWord ++ tailWord_787072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787142 : List Nat := [6, 1, 2, 1, 2, 2, 2, 1, 5]
def baseStart_787142 : Nat := 118140960795 + 787142 * 2 ^ 59
def prefixEnd_787142 : Nat := 4983230072969 + 3 ^ 40 * 787142 * 2
def baseEnd_787142 : Nat := 89818264298103230445557

theorem tailTrace_787142 : CollatzResearch.WordTrace tailWord_787142 prefixEnd_787142 89818264298103230445557 := by
  unfold tailWord_787142
  simp only [CollatzResearch.WordTrace]
  refine ⟨897169603572701312373115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19139618209550961330626453 897169603572701312373115)
  ·
    refine ⟨1345754405359051968559673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 897169603572701312373115 1345754405359051968559673)
    ·
      refine ⟨1009315804019288976419755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1345754405359051968559673 1009315804019288976419755)
      ·
        refine ⟨1513973706028933464629633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1009315804019288976419755 1513973706028933464629633)
        ·
          refine ⟨1135480279521700098472225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1513973706028933464629633 1135480279521700098472225)
          ·
            refine ⟨851610209641275073854169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1135480279521700098472225 851610209641275073854169)
            ·
              refine ⟨638707657230956305390627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 851610209641275073854169 638707657230956305390627)
              ·
                refine ⟨958061485846434458085941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 638707657230956305390627 958061485846434458085941)
                ·
                  refine ⟨89818264298103230445557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 958061485846434458085941 89818264298103230445557)
                  ·
                    rfl

theorem cell22_787142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_787142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_787142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_787142 prefixEnd_787142 := by exact prefixLift 787142
  have htrace : WordTrace (prefixWord ++ tailWord_787142) baseStart_787142 baseEnd_787142 := by
    simpa [prefixWord, tailWord_787142, baseEnd_787142] using wordTrace_append hprefix tailTrace_787142
  have hstable : (prefixWord ++ tailWord_787142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787142).length < 2 ^ (prefixWord ++ tailWord_787142).sum := by decide
  have hdescent : baseEnd_787142 < baseStart_787142 := by decide
  rcases family_descends (prefixWord ++ tailWord_787142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787209 : List Nat := [1, 2, 1, 1, 3, 2, 4, 3, 5]
def baseStart_787209 : Nat := 118140960795 + 787209 * 2 ^ 59
def prefixEnd_787209 : Nat := 4983230072969 + 3 ^ 40 * 787209 * 2
def baseEnd_787209 : Nat := 89825909454514616637155

theorem tailTrace_787209 : CollatzResearch.WordTrace tailWord_787209 prefixEnd_787209 89825909454514616637155 := by
  unfold tailWord_787209
  simp only [CollatzResearch.WordTrace]
  refine ⟨28711871005083712438628681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19141247336722474959085787 28711871005083712438628681)
  ·
    refine ⟨21533903253812784328971511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28711871005083712438628681 21533903253812784328971511)
    ·
      refine ⟨32300854880719176493457267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21533903253812784328971511 32300854880719176493457267)
      ·
        refine ⟨48451282321078764740185901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32300854880719176493457267 48451282321078764740185901)
        ·
          refine ⟨18169230870404536777569713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48451282321078764740185901 18169230870404536777569713)
          ·
            refine ⟨13626923152803402583177285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18169230870404536777569713 13626923152803402583177285)
            ·
              refine ⟨2555048091150637984345741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13626923152803402583177285 2555048091150637984345741)
              ·
                refine ⟨958143034181489244129653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2555048091150637984345741 958143034181489244129653)
                ·
                  refine ⟨89825909454514616637155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 958143034181489244129653 89825909454514616637155)
                  ·
                    rfl

theorem cell22_787209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 3, 5].length) (baseStart_787209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_787209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_787209 prefixEnd_787209 := by exact prefixLift 787209
  have htrace : WordTrace (prefixWord ++ tailWord_787209) baseStart_787209 baseEnd_787209 := by
    simpa [prefixWord, tailWord_787209, baseEnd_787209] using wordTrace_append hprefix tailTrace_787209
  have hstable : (prefixWord ++ tailWord_787209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787209).length < 2 ^ (prefixWord ++ tailWord_787209).sum := by decide
  have hdescent : baseEnd_787209 < baseStart_787209 := by decide
  rcases family_descends (prefixWord ++ tailWord_787209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787269 : List Nat := [1, 3, 1, 1, 1, 2, 2, 5, 1, 5]
def baseStart_787269 : Nat := 118140960795 + 787269 * 2 ^ 59
def prefixEnd_787269 : Nat := 4983230072969 + 3 ^ 40 * 787269 * 2
def baseEnd_787269 : Nat := 269498267589723693411281

theorem tailTrace_787269 : CollatzResearch.WordTrace tailWord_787269 prefixEnd_787269 269498267589723693411281 := by
  unfold tailWord_787269
  simp only [CollatzResearch.WordTrace]
  refine ⟨28714059384866342685812861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19142706256577561790541907 28714059384866342685812861)
  ·
    refine ⟨10767772269324878507179823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28714059384866342685812861 10767772269324878507179823)
    ·
      refine ⟨16151658403987317760769735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10767772269324878507179823 16151658403987317760769735)
      ·
        refine ⟨24227487605980976641154603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16151658403987317760769735 24227487605980976641154603)
        ·
          refine ⟨36341231408971464961731905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24227487605980976641154603 36341231408971464961731905)
          ·
            refine ⟨27255923556728598721298929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36341231408971464961731905 27255923556728598721298929)
            ·
              refine ⟨20441942667546449040974197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27255923556728598721298929 20441942667546449040974197)
              ·
                refine ⟨1916432125082479597591331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20441942667546449040974197 1916432125082479597591331)
                ·
                  refine ⟨2874648187623719396386997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1916432125082479597591331 2874648187623719396386997)
                  ·
                    refine ⟨269498267589723693411281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2874648187623719396386997 269498267589723693411281)
                    ·
                      rfl

theorem cell22_787269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 5].length) (baseStart_787269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_787269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_787269 prefixEnd_787269 := by exact prefixLift 787269
  have htrace : WordTrace (prefixWord ++ tailWord_787269) baseStart_787269 baseEnd_787269 := by
    simpa [prefixWord, tailWord_787269, baseEnd_787269] using wordTrace_append hprefix tailTrace_787269
  have hstable : (prefixWord ++ tailWord_787269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787269).length < 2 ^ (prefixWord ++ tailWord_787269).sum := by decide
  have hdescent : baseEnd_787269 < baseStart_787269 := by decide
  rcases family_descends (prefixWord ++ tailWord_787269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787299 : List Nat := [1, 1, 1, 5, 3, 1, 10]
def baseStart_787299 : Nat := 118140960795 + 787299 * 2 ^ 59
def prefixEnd_787299 : Nat := 4983230072969 + 3 ^ 40 * 787299 * 2
def baseEnd_787299 : Nat := 9981797674178282043007

theorem tailTrace_787299 : CollatzResearch.WordTrace tailWord_787299 prefixEnd_787299 9981797674178282043007 := by
  unfold tailWord_787299
  simp only [CollatzResearch.WordTrace]
  refine ⟨28715153574757657809404951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19143435716505105206269967 28715153574757657809404951)
  ·
    refine ⟨43072730362136486714107427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28715153574757657809404951 43072730362136486714107427)
    ·
      refine ⟨64609095543204730071161141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43072730362136486714107427 64609095543204730071161141)
      ·
        refine ⟨6057102707175443444171357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64609095543204730071161141 6057102707175443444171357)
        ·
          refine ⟨2271413515190791291564259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6057102707175443444171357 2271413515190791291564259)
          ·
            refine ⟨3407120272786186937346389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2271413515190791291564259 3407120272786186937346389)
            ·
              refine ⟨9981797674178282043007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3407120272786186937346389 9981797674178282043007)
              ·
                rfl

theorem cell22_787299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 10].length) (baseStart_787299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_787299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_787299 prefixEnd_787299 := by exact prefixLift 787299
  have htrace : WordTrace (prefixWord ++ tailWord_787299) baseStart_787299 baseEnd_787299 := by
    simpa [prefixWord, tailWord_787299, baseEnd_787299] using wordTrace_append hprefix tailTrace_787299
  have hstable : (prefixWord ++ tailWord_787299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787299).length < 2 ^ (prefixWord ++ tailWord_787299).sum := by decide
  have hdescent : baseEnd_787299 < baseStart_787299 := by decide
  rcases family_descends (prefixWord ++ tailWord_787299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787331 : List Nat := [1, 1, 1, 3, 4, 1, 2, 1, 5, 3]
def baseStart_787331 : Nat := 118140960795 + 787331 * 2 ^ 59
def prefixEnd_787331 : Nat := 4983230072969 + 3 ^ 40 * 787331 * 2
def baseEnd_787331 : Nat := 269519491456776198361091

theorem tailTrace_787331 : CollatzResearch.WordTrace tailWord_787331 prefixEnd_787331 269519491456776198361091 := by
  unfold tailWord_787331
  simp only [CollatzResearch.WordTrace]
  refine ⟨28716320710641727274569847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19144213807094484849713231 28716320710641727274569847)
  ·
    refine ⟨43074481065962590911854771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28716320710641727274569847 43074481065962590911854771)
    ·
      refine ⟨64611721598943886367782157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43074481065962590911854771 64611721598943886367782157)
      ·
        refine ⟨24229395599603957387918309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64611721598943886367782157 24229395599603957387918309)
        ·
          refine ⟨4543011674925742010234683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24229395599603957387918309 4543011674925742010234683)
          ·
            refine ⟨6814517512388613015352025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4543011674925742010234683 6814517512388613015352025)
            ·
              refine ⟨5110888134291459761514019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6814517512388613015352025 5110888134291459761514019)
              ·
                refine ⟨7666332201437189642271029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5110888134291459761514019 7666332201437189642271029)
                ·
                  refine ⟨718718643884736528962909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7666332201437189642271029 718718643884736528962909)
                  ·
                    refine ⟨269519491456776198361091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 718718643884736528962909 269519491456776198361091)
                    ·
                      rfl

theorem cell22_787331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 5, 3].length) (baseStart_787331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_787331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_787331 prefixEnd_787331 := by exact prefixLift 787331
  have htrace : WordTrace (prefixWord ++ tailWord_787331) baseStart_787331 baseEnd_787331 := by
    simpa [prefixWord, tailWord_787331, baseEnd_787331] using wordTrace_append hprefix tailTrace_787331
  have hstable : (prefixWord ++ tailWord_787331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787331).length < 2 ^ (prefixWord ++ tailWord_787331).sum := by decide
  have hdescent : baseEnd_787331 < baseStart_787331 := by decide
  rcases family_descends (prefixWord ++ tailWord_787331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787423 : List Nat := [1, 1, 2, 3, 5, 1, 2, 1, 6]
def baseStart_787423 : Nat := 118140960795 + 787423 * 2 ^ 59
def prefixEnd_787423 : Nat := 4983230072969 + 3 ^ 40 * 787423 * 2
def baseEnd_787423 : Nat := 89850328312306208353603

theorem tailTrace_787423 : CollatzResearch.WordTrace tailWord_787423 prefixEnd_787423 89850328312306208353603 := by
  unfold tailWord_787423
  simp only [CollatzResearch.WordTrace]
  refine ⟨28719676226308426986918923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19146450817538951324612615 28719676226308426986918923)
  ·
    refine ⟨43079514339462640480378385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28719676226308426986918923 43079514339462640480378385)
    ·
      refine ⟨32309635754596980360283789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43079514339462640480378385 32309635754596980360283789)
      ·
        refine ⟨12116113407973867635106421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32309635754596980360283789 12116113407973867635106421)
        ·
          refine ⟨1135885631997550090791227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12116113407973867635106421 1135885631997550090791227)
          ·
            refine ⟨1703828447996325136186841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1135885631997550090791227 1703828447996325136186841)
            ·
              refine ⟨1277871335997243852140131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1703828447996325136186841 1277871335997243852140131)
              ·
                refine ⟨1916807003995865778210197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1277871335997243852140131 1916807003995865778210197)
                ·
                  refine ⟨89850328312306208353603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1916807003995865778210197 89850328312306208353603)
                  ·
                    rfl

theorem cell22_787423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 6].length) (baseStart_787423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_787423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_787423 prefixEnd_787423 := by exact prefixLift 787423
  have htrace : WordTrace (prefixWord ++ tailWord_787423) baseStart_787423 baseEnd_787423 := by
    simpa [prefixWord, tailWord_787423, baseEnd_787423] using wordTrace_append hprefix tailTrace_787423
  have hstable : (prefixWord ++ tailWord_787423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787423).length < 2 ^ (prefixWord ++ tailWord_787423).sum := by decide
  have hdescent : baseEnd_787423 < baseStart_787423 := by decide
  rcases family_descends (prefixWord ++ tailWord_787423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787442 : List Nat := [3, 2, 1, 5, 1, 1, 2, 2, 1, 4]
def baseStart_787442 : Nat := 118140960795 + 787442 * 2 ^ 59
def prefixEnd_787442 : Nat := 4983230072969 + 3 ^ 40 * 787442 * 2
def baseEnd_787442 : Nat := 269557489025208908835751

theorem tailTrace_787442 : CollatzResearch.WordTrace tailWord_787442 prefixEnd_787442 269557489025208908835751 := by
  unfold tailWord_787442
  simp only [CollatzResearch.WordTrace]
  refine ⟨7180092303309898307965145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19146912808826395487907053 7180092303309898307965145)
  ·
    refine ⟨5385069227482423730973859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7180092303309898307965145 5385069227482423730973859)
    ·
      refine ⟨8077603841223635596460789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5385069227482423730973859 8077603841223635596460789)
      ·
        refine ⟨757275360114715837168199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8077603841223635596460789 757275360114715837168199)
        ·
          refine ⟨1135913040172073755752299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 757275360114715837168199 1135913040172073755752299)
          ·
            refine ⟨1703869560258110633628449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1135913040172073755752299 1703869560258110633628449)
            ·
              refine ⟨1277902170193582975221337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1703869560258110633628449 1277902170193582975221337)
              ·
                refine ⟨958426627645187231416003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1277902170193582975221337 958426627645187231416003)
                ·
                  refine ⟨1437639941467780847124005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 958426627645187231416003 1437639941467780847124005)
                  ·
                    refine ⟨269557489025208908835751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1437639941467780847124005 269557489025208908835751)
                    ·
                      rfl

theorem cell22_787442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 2, 1, 4].length) (baseStart_787442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_787442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_787442 prefixEnd_787442 := by exact prefixLift 787442
  have htrace : WordTrace (prefixWord ++ tailWord_787442) baseStart_787442 baseEnd_787442 := by
    simpa [prefixWord, tailWord_787442, baseEnd_787442] using wordTrace_append hprefix tailTrace_787442
  have hstable : (prefixWord ++ tailWord_787442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787442).length < 2 ^ (prefixWord ++ tailWord_787442).sum := by decide
  have hdescent : baseEnd_787442 < baseStart_787442 := by decide
  rcases family_descends (prefixWord ++ tailWord_787442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787474 : List Nat := [3, 2, 5, 1, 1, 2, 1, 1, 6]
def baseStart_787474 : Nat := 118140960795 + 787474 * 2 ^ 59
def prefixEnd_787474 : Nat := 4983230072969 + 3 ^ 40 * 787474 * 2
def baseEnd_787474 : Nat := 89856147759723830678551

theorem tailTrace_787474 : CollatzResearch.WordTrace tailWord_787474 prefixEnd_787474 89856147759723830678551 := by
  unfold tailWord_787474
  simp only [CollatzResearch.WordTrace]
  refine ⟨7180384087280915674256369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19147690899415775131350317 7180384087280915674256369)
  ·
    refine ⟨5385288065460686755692277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7180384087280915674256369 5385288065460686755692277)
    ·
      refine ⟨504870756136939383346151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5385288065460686755692277 504870756136939383346151)
      ·
        refine ⟨757306134205409075019227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 504870756136939383346151 757306134205409075019227)
        ·
          refine ⟨1135959201308113612528841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 757306134205409075019227 1135959201308113612528841)
          ·
            refine ⟨851969400981085209396631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1135959201308113612528841 851969400981085209396631)
            ·
              refine ⟨1277954101471627814094947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 851969400981085209396631 1277954101471627814094947)
              ·
                refine ⟨1916931152207441721142421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1277954101471627814094947 1916931152207441721142421)
                ·
                  refine ⟨89856147759723830678551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1916931152207441721142421 89856147759723830678551)
                  ·
                    rfl

theorem cell22_787474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 6].length) (baseStart_787474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_787474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_787474 prefixEnd_787474 := by exact prefixLift 787474
  have htrace : WordTrace (prefixWord ++ tailWord_787474) baseStart_787474 baseEnd_787474 := by
    simpa [prefixWord, tailWord_787474, baseEnd_787474] using wordTrace_append hprefix tailTrace_787474
  have hstable : (prefixWord ++ tailWord_787474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787474).length < 2 ^ (prefixWord ++ tailWord_787474).sum := by decide
  have hdescent : baseEnd_787474 < baseStart_787474 := by decide
  rcases family_descends (prefixWord ++ tailWord_787474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787511 : List Nat := [1, 1, 3, 1, 2, 2, 1, 2, 4, 5]
def baseStart_787511 : Nat := 118140960795 + 787511 * 2 ^ 59
def prefixEnd_787511 : Nat := 4983230072969 + 3 ^ 40 * 787511 * 2
def baseEnd_787511 : Nat := 269581109135315728860539

theorem tailTrace_787511 : CollatzResearch.WordTrace tailWord_787511 prefixEnd_787511 269581109135315728860539 := by
  unfold tailWord_787511
  simp only [CollatzResearch.WordTrace]
  refine ⟨28722885849989618016122387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19148590566659745344081591 28722885849989618016122387)
  ·
    refine ⟨43084328774984427024183581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28722885849989618016122387 43084328774984427024183581)
    ·
      refine ⟨16156623290619160134068843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43084328774984427024183581 16156623290619160134068843)
      ·
        refine ⟨24234934935928740201103265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16156623290619160134068843 24234934935928740201103265)
        ·
          refine ⟨18176201201946555150827449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24234934935928740201103265 18176201201946555150827449)
          ·
            refine ⟨13632150901459916363120587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18176201201946555150827449 13632150901459916363120587)
            ·
              refine ⟨20448226352189874544680881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13632150901459916363120587 20448226352189874544680881)
              ·
                refine ⟨15336169764142405908510661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20448226352189874544680881 15336169764142405908510661)
                ·
                  refine ⟨2875531830776701107845749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15336169764142405908510661 2875531830776701107845749)
                  ·
                    refine ⟨269581109135315728860539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2875531830776701107845749 269581109135315728860539)
                    ·
                      rfl

theorem cell22_787511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 5].length) (baseStart_787511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_787511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_787511 prefixEnd_787511 := by exact prefixLift 787511
  have htrace : WordTrace (prefixWord ++ tailWord_787511) baseStart_787511 baseEnd_787511 := by
    simpa [prefixWord, tailWord_787511, baseEnd_787511] using wordTrace_append hprefix tailTrace_787511
  have hstable : (prefixWord ++ tailWord_787511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787511).length < 2 ^ (prefixWord ++ tailWord_787511).sum := by decide
  have hdescent : baseEnd_787511 < baseStart_787511 := by decide
  rcases family_descends (prefixWord ++ tailWord_787511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787575 : List Nat := [1, 1, 3, 1, 1, 4, 4, 3, 4]
def baseStart_787575 : Nat := 118140960795 + 787575 * 2 ^ 59
def prefixEnd_787575 : Nat := 4983230072969 + 3 ^ 40 * 787575 * 2
def baseEnd_787575 : Nat := 89867672547746965086781

theorem tailTrace_787575 : CollatzResearch.WordTrace tailWord_787575 prefixEnd_787575 89867672547746965086781 := by
  unfold tailWord_787575
  simp only [CollatzResearch.WordTrace]
  refine ⟨28725220121757756946452179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19150146747838504630968119 28725220121757756946452179)
  ·
    refine ⟨43087830182636635419678269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28725220121757756946452179 43087830182636635419678269)
    ·
      refine ⟨16157936318488738282379351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43087830182636635419678269 16157936318488738282379351)
      ·
        refine ⟨24236904477733107423569027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16157936318488738282379351 24236904477733107423569027)
        ·
          refine ⟨36355356716599661135353541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24236904477733107423569027 36355356716599661135353541)
          ·
            refine ⟨6816629384362436462878789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36355356716599661135353541 6816629384362436462878789)
            ·
              refine ⟨1278118009567956836789773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6816629384362436462878789 1278118009567956836789773)
              ·
                refine ⟨479294253587983813796165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1278118009567956836789773 479294253587983813796165)
                ·
                  refine ⟨89867672547746965086781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 479294253587983813796165 89867672547746965086781)
                  ·
                    rfl

theorem cell22_787575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 3, 4].length) (baseStart_787575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_787575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_787575 prefixEnd_787575 := by exact prefixLift 787575
  have htrace : WordTrace (prefixWord ++ tailWord_787575) baseStart_787575 baseEnd_787575 := by
    simpa [prefixWord, tailWord_787575, baseEnd_787575] using wordTrace_append hprefix tailTrace_787575
  have hstable : (prefixWord ++ tailWord_787575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787575).length < 2 ^ (prefixWord ++ tailWord_787575).sum := by decide
  have hdescent : baseEnd_787575 < baseStart_787575 := by decide
  rcases family_descends (prefixWord ++ tailWord_787575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787620 : List Nat := [2, 3, 1, 2, 3, 1, 4, 6]
def baseStart_787620 : Nat := 118140960795 + 787620 * 2 ^ 59
def prefixEnd_787620 : Nat := 4983230072969 + 3 ^ 40 * 787620 * 2
def baseEnd_787620 : Nat := 29957602451430641987245

theorem tailTrace_787620 : CollatzResearch.WordTrace tailWord_787620 prefixEnd_787620 29957602451430641987245 := by
  unfold tailWord_787620
  simp only [CollatzResearch.WordTrace]
  refine ⟨14363430703297364815920157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19151240937729819754560209 14363430703297364815920157)
  ·
    refine ⟨5386286513736511805970059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14363430703297364815920157 5386286513736511805970059)
    ·
      refine ⟨8079429770604767708955089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5386286513736511805970059 8079429770604767708955089)
      ·
        refine ⟨6059572327953575781716317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8079429770604767708955089 6059572327953575781716317)
        ·
          refine ⟨2272339622982590918143619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6059572327953575781716317 2272339622982590918143619)
          ·
            refine ⟨3408509434473886377215429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2272339622982590918143619 3408509434473886377215429)
            ·
              refine ⟨639095518963853695727893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3408509434473886377215429 639095518963853695727893)
              ·
                refine ⟨29957602451430641987245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 639095518963853695727893 29957602451430641987245)
                ·
                  rfl

theorem cell22_787620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 6].length) (baseStart_787620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_787620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_787620 prefixEnd_787620 := by exact prefixLift 787620
  have htrace : WordTrace (prefixWord ++ tailWord_787620) baseStart_787620 baseEnd_787620 := by
    simpa [prefixWord, tailWord_787620, baseEnd_787620] using wordTrace_append hprefix tailTrace_787620
  have hstable : (prefixWord ++ tailWord_787620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787620).length < 2 ^ (prefixWord ++ tailWord_787620).sum := by decide
  have hdescent : baseEnd_787620 < baseStart_787620 := by decide
  rcases family_descends (prefixWord ++ tailWord_787620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787744 : List Nat := [2, 1, 1, 5, 3, 1, 2, 3, 4]
def baseStart_787744 : Nat := 118140960795 + 787744 * 2 ^ 59
def prefixEnd_787744 : Nat := 4983230072969 + 3 ^ 40 * 787744 * 2
def baseEnd_787744 : Nat := 89886956598993595928275

theorem tailTrace_787744 : CollatzResearch.WordTrace tailWord_787744 prefixEnd_787744 89886956598993595928275 := by
  unfold tailWord_787744
  simp only [CollatzResearch.WordTrace]
  refine ⟨14365692029072749404677143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19154256038763665872902857 14365692029072749404677143)
  ·
    refine ⟨21548538043609124107015715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14365692029072749404677143 21548538043609124107015715)
    ·
      refine ⟨32322807065413686160523573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21548538043609124107015715 32322807065413686160523573)
      ·
        refine ⟨3030263162382533077549085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32322807065413686160523573 3030263162382533077549085)
        ·
          refine ⟨1136348685893449904080907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3030263162382533077549085 1136348685893449904080907)
          ·
            refine ⟨1704523028840174856121361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1136348685893449904080907 1704523028840174856121361)
            ·
              refine ⟨1278392271630131142091021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1704523028840174856121361 1278392271630131142091021)
              ·
                refine ⟨479397101861299178284133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1278392271630131142091021 479397101861299178284133)
                ·
                  refine ⟨89886956598993595928275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 479397101861299178284133 89886956598993595928275)
                  ·
                    rfl

theorem cell22_787744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 3, 4].length) (baseStart_787744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_787744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_787744 prefixEnd_787744 := by exact prefixLift 787744
  have htrace : WordTrace (prefixWord ++ tailWord_787744) baseStart_787744 baseEnd_787744 := by
    simpa [prefixWord, tailWord_787744, baseEnd_787744] using wordTrace_append hprefix tailTrace_787744
  have hstable : (prefixWord ++ tailWord_787744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787744).length < 2 ^ (prefixWord ++ tailWord_787744).sum := by decide
  have hdescent : baseEnd_787744 < baseStart_787744 := by decide
  rcases family_descends (prefixWord ++ tailWord_787744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787746 : List Nat := [3, 3, 1, 1, 4, 2, 2, 1, 1, 4]
def baseStart_787746 : Nat := 118140960795 + 787746 * 2 ^ 59
def prefixEnd_787746 : Nat := 4983230072969 + 3 ^ 40 * 787746 * 2
def baseEnd_787746 : Nat := 269661554437853449234819

theorem tailTrace_787746 : CollatzResearch.WordTrace tailWord_787746 prefixEnd_787746 269661554437853449234819 := by
  unfold tailWord_787746
  simp only [CollatzResearch.WordTrace]
  refine ⟨7182864251034563287731773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19154304669425502100618061 7182864251034563287731773)
  ·
    refine ⟨2693574094137961232899415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7182864251034563287731773 2693574094137961232899415)
    ·
      refine ⟨4040361141206941849349123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2693574094137961232899415 4040361141206941849349123)
      ·
        refine ⟨6060541711810412774023685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4040361141206941849349123 6060541711810412774023685)
        ·
          refine ⟨1136351570964452395129441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6060541711810412774023685 1136351570964452395129441)
          ·
            refine ⟨852263678223339296347081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1136351570964452395129441 852263678223339296347081)
            ·
              refine ⟨639197758667504472260311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 852263678223339296347081 639197758667504472260311)
              ·
                refine ⟨958796638001256708390467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 639197758667504472260311 958796638001256708390467)
                ·
                  refine ⟨1438194957001885062585701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 958796638001256708390467 1438194957001885062585701)
                  ·
                    refine ⟨269661554437853449234819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1438194957001885062585701 269661554437853449234819)
                    ·
                      rfl

theorem cell22_787746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_787746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_787746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_787746 prefixEnd_787746 := by exact prefixLift 787746
  have htrace : WordTrace (prefixWord ++ tailWord_787746) baseStart_787746 baseEnd_787746 := by
    simpa [prefixWord, tailWord_787746, baseEnd_787746] using wordTrace_append hprefix tailTrace_787746
  have hstable : (prefixWord ++ tailWord_787746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787746).length < 2 ^ (prefixWord ++ tailWord_787746).sum := by decide
  have hdescent : baseEnd_787746 < baseStart_787746 := by decide
  rcases family_descends (prefixWord ++ tailWord_787746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787789 : List Nat := [1, 6, 1, 3, 1, 1, 1, 8]
def baseStart_787789 : Nat := 118140960795 + 787789 * 2 ^ 59
def prefixEnd_787789 : Nat := 4983230072969 + 3 ^ 40 * 787789 * 2
def baseEnd_787789 : Nat := 29964030468512852267743

theorem tailTrace_787789 : CollatzResearch.WordTrace tailWord_787789 prefixEnd_787789 29964030468512852267743 := by
  unfold tailWord_787789
  simp only [CollatzResearch.WordTrace]
  refine ⟨28733025342982471494742421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19155350228654980996494947 28733025342982471494742421)
  ·
    refine ⟨1346860562952303351316051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 28733025342982471494742421 1346860562952303351316051)
    ·
      refine ⟨2020290844428455026974077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1346860562952303351316051 2020290844428455026974077)
      ·
        refine ⟨757609066660670635115279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2020290844428455026974077 757609066660670635115279)
        ·
          refine ⟨1136413599991005952672919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 757609066660670635115279 1136413599991005952672919)
          ·
            refine ⟨1704620399986508929009379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1136413599991005952672919 1704620399986508929009379)
            ·
              refine ⟨2556930599979763393514069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1704620399986508929009379 2556930599979763393514069)
              ·
                refine ⟨29964030468512852267743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2556930599979763393514069 29964030468512852267743)
                ·
                  rfl

theorem cell22_787789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 8].length) (baseStart_787789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_787789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_787789 prefixEnd_787789 := by exact prefixLift 787789
  have htrace : WordTrace (prefixWord ++ tailWord_787789) baseStart_787789 baseEnd_787789 := by
    simpa [prefixWord, tailWord_787789, baseEnd_787789] using wordTrace_append hprefix tailTrace_787789
  have hstable : (prefixWord ++ tailWord_787789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787789).length < 2 ^ (prefixWord ++ tailWord_787789).sum := by decide
  have hdescent : baseEnd_787789 < baseStart_787789 := by decide
  rcases family_descends (prefixWord ++ tailWord_787789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787845 : List Nat := [1, 3, 1, 1, 3, 1, 2, 4, 6]
def baseStart_787845 : Nat := 118140960795 + 787845 * 2 ^ 59
def prefixEnd_787845 : Nat := 4983230072969 + 3 ^ 40 * 787845 * 2
def baseEnd_787845 : Nat := 89898481387016730336505

theorem tailTrace_787845 : CollatzResearch.WordTrace tailWord_787845 prefixEnd_787845 89898481387016730336505 := by
  unfold tailWord_787845
  simp only [CollatzResearch.WordTrace]
  refine ⟨28735067830779593058780989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19156711887186395372520659 28735067830779593058780989)
  ·
    refine ⟨10775650436542347397042871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28735067830779593058780989 10775650436542347397042871)
    ·
      refine ⟨16163475654813521095564307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10775650436542347397042871 16163475654813521095564307)
      ·
        refine ⟨24245213482220281643346461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16163475654813521095564307 24245213482220281643346461)
        ·
          refine ⟨9091955055832605616254923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24245213482220281643346461 9091955055832605616254923)
          ·
            refine ⟨13637932583748908424382385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9091955055832605616254923 13637932583748908424382385)
            ·
              refine ⟨10228449437811681318286789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13637932583748908424382385 10228449437811681318286789)
              ·
                refine ⟨1917834269589690247178773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10228449437811681318286789 1917834269589690247178773)
                ·
                  refine ⟨89898481387016730336505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1917834269589690247178773 89898481387016730336505)
                  ·
                    rfl

theorem cell22_787845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 6].length) (baseStart_787845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_787845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_787845 prefixEnd_787845 := by exact prefixLift 787845
  have htrace : WordTrace (prefixWord ++ tailWord_787845) baseStart_787845 baseEnd_787845 := by
    simpa [prefixWord, tailWord_787845, baseEnd_787845] using wordTrace_append hprefix tailTrace_787845
  have hstable : (prefixWord ++ tailWord_787845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787845).length < 2 ^ (prefixWord ++ tailWord_787845).sum := by decide
  have hdescent : baseEnd_787845 < baseStart_787845 := by decide
  rcases family_descends (prefixWord ++ tailWord_787845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787847 : List Nat := [1, 1, 4, 2, 2, 3, 1, 1, 3, 4]
def baseStart_787847 : Nat := 118140960795 + 787847 * 2 ^ 59
def prefixEnd_787847 : Nat := 4983230072969 + 3 ^ 40 * 787847 * 2
def baseEnd_787847 : Nat := 269696128801922852459509

theorem tailTrace_787847 : CollatzResearch.WordTrace tailWord_787847 prefixEnd_787847 269696128801922852459509 := by
  unfold tailWord_787847
  simp only [CollatzResearch.WordTrace]
  refine ⟨28735140776772347400353795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19156760517848231600235863 28735140776772347400353795)
  ·
    refine ⟨43102711165158521100530693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28735140776772347400353795 43102711165158521100530693)
    ·
      refine ⟨8081758343467222706349505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43102711165158521100530693 8081758343467222706349505)
      ·
        refine ⟨6061318757600417029762129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8081758343467222706349505 6061318757600417029762129)
        ·
          refine ⟨4545989068200312772321597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6061318757600417029762129 4545989068200312772321597)
          ·
            refine ⟨1704745900575117289620599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4545989068200312772321597 1704745900575117289620599)
            ·
              refine ⟨2557118850862675934430899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1704745900575117289620599 2557118850862675934430899)
              ·
                refine ⟨3835678276294013901646349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2557118850862675934430899 3835678276294013901646349)
                ·
                  refine ⟨1438379353610255213117381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3835678276294013901646349 1438379353610255213117381)
                  ·
                    refine ⟨269696128801922852459509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1438379353610255213117381 269696128801922852459509)
                    ·
                      rfl

theorem cell22_787847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_787847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_787847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_787847 prefixEnd_787847 := by exact prefixLift 787847
  have htrace : WordTrace (prefixWord ++ tailWord_787847) baseStart_787847 baseEnd_787847 := by
    simpa [prefixWord, tailWord_787847, baseEnd_787847] using wordTrace_append hprefix tailTrace_787847
  have hstable : (prefixWord ++ tailWord_787847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787847).length < 2 ^ (prefixWord ++ tailWord_787847).sum := by decide
  have hdescent : baseEnd_787847 < baseStart_787847 := by decide
  rcases family_descends (prefixWord ++ tailWord_787847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787879 : List Nat := [1, 1, 6, 1, 1, 1, 3, 4, 4]
def baseStart_787879 : Nat := 118140960795 + 787879 * 2 ^ 59
def prefixEnd_787879 : Nat := 4983230072969 + 3 ^ 40 * 787879 * 2
def baseEnd_787879 : Nat := 89902361018628478553137

theorem tailTrace_787879 : CollatzResearch.WordTrace tailWord_787879 prefixEnd_787879 89902361018628478553137 := by
  unfold tailWord_787879
  simp only [CollatzResearch.WordTrace]
  refine ⟨28736307912656416865518691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19157538608437611243679127 28736307912656416865518691)
  ·
    refine ⟨43104461868984625298278037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28736307912656416865518691 43104461868984625298278037)
    ·
      refine ⟨2020521650108654310856783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 43104461868984625298278037 2020521650108654310856783)
      ·
        refine ⟨3030782475162981466285175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2020521650108654310856783 3030782475162981466285175)
        ·
          refine ⟨4546173712744472199427763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3030782475162981466285175 4546173712744472199427763)
          ·
            refine ⟨6819260569116708299141645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4546173712744472199427763 6819260569116708299141645)
            ·
              refine ⟨2557222713418765612178117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6819260569116708299141645 2557222713418765612178117)
              ·
                refine ⟨479479258766018552283397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2557222713418765612178117 479479258766018552283397)
                ·
                  refine ⟨89902361018628478553137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 479479258766018552283397 89902361018628478553137)
                  ·
                    rfl

theorem cell22_787879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 4, 4].length) (baseStart_787879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_787879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_787879 prefixEnd_787879 := by exact prefixLift 787879
  have htrace : WordTrace (prefixWord ++ tailWord_787879) baseStart_787879 baseEnd_787879 := by
    simpa [prefixWord, tailWord_787879, baseEnd_787879] using wordTrace_append hprefix tailTrace_787879
  have hstable : (prefixWord ++ tailWord_787879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787879).length < 2 ^ (prefixWord ++ tailWord_787879).sum := by decide
  have hdescent : baseEnd_787879 < baseStart_787879 := by decide
  rcases family_descends (prefixWord ++ tailWord_787879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787890 : List Nat := [3, 2, 1, 1, 1, 1, 2, 11]
def baseStart_787890 : Nat := 118140960795 + 787890 * 2 ^ 59
def prefixEnd_787890 : Nat := 4983230072969 + 3 ^ 40 * 787890 * 2
def baseEnd_787890 : Nat := 29967872064520563737153

theorem tailTrace_787890 : CollatzResearch.WordTrace tailWord_787890 prefixEnd_787890 29967872064520563737153 := by
  unfold tailWord_787890
  simp only [CollatzResearch.WordTrace]
  refine ⟨7184177278904141436042281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19157806077077710496112749 7184177278904141436042281)
  ·
    refine ⟨5388132959178106077031711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7184177278904141436042281 5388132959178106077031711)
    ·
      refine ⟨8082199438767159115547567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5388132959178106077031711 8082199438767159115547567)
      ·
        refine ⟨12123299158150738673321351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8082199438767159115547567 12123299158150738673321351)
        ·
          refine ⟨18184948737226108009982027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12123299158150738673321351 18184948737226108009982027)
          ·
            refine ⟨27277423105839162014973041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18184948737226108009982027 27277423105839162014973041)
            ·
              refine ⟨20458067329379371511229781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27277423105839162014973041 20458067329379371511229781)
              ·
                refine ⟨29967872064520563737153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 20458067329379371511229781 29967872064520563737153)
                ·
                  rfl

theorem cell22_787890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 11].length) (baseStart_787890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_787890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_787890 prefixEnd_787890 := by exact prefixLift 787890
  have htrace : WordTrace (prefixWord ++ tailWord_787890) baseStart_787890 baseEnd_787890 := by
    simpa [prefixWord, tailWord_787890, baseEnd_787890] using wordTrace_append hprefix tailTrace_787890
  have hstable : (prefixWord ++ tailWord_787890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787890).length < 2 ^ (prefixWord ++ tailWord_787890).sum := by decide
  have hdescent : baseEnd_787890 < baseStart_787890 := by decide
  rcases family_descends (prefixWord ++ tailWord_787890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787920 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 4, 6]
def baseStart_787920 : Nat := 118140960795 + 787920 * 2 ^ 59
def prefixEnd_787920 : Nat := 4983230072969 + 3 ^ 40 * 787920 * 2
def baseEnd_787920 : Nat := 269721118193774995384285

theorem tailTrace_787920 : CollatzResearch.WordTrace tailWord_787920 prefixEnd_787920 269721118193774995384285 := by
  unfold tailWord_787920
  simp only [CollatzResearch.WordTrace]
  refine ⟨14368901652753940433880607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19158535537005253911840809 14368901652753940433880607)
  ·
    refine ⟨21553352479130910650820911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14368901652753940433880607 21553352479130910650820911)
    ·
      refine ⟨32330028718696365976231367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21553352479130910650820911 32330028718696365976231367)
      ·
        refine ⟨48495043078044548964347051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32330028718696365976231367 48495043078044548964347051)
        ·
          refine ⟨72742564617066823446520577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48495043078044548964347051 72742564617066823446520577)
          ·
            refine ⟨54556923462800117584890433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72742564617066823446520577 54556923462800117584890433)
            ·
              refine ⟨40917692597100088188667825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54556923462800117584890433 40917692597100088188667825)
              ·
                refine ⟨30688269447825066141500869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40917692597100088188667825 30688269447825066141500869)
                ·
                  refine ⟨5754050521467199901531413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30688269447825066141500869 5754050521467199901531413)
                  ·
                    refine ⟨269721118193774995384285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5754050521467199901531413 269721118193774995384285)
                    ·
                      rfl

theorem cell22_787920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 4, 6].length) (baseStart_787920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_787920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_787920 prefixEnd_787920 := by exact prefixLift 787920
  have htrace : WordTrace (prefixWord ++ tailWord_787920) baseStart_787920 baseEnd_787920 := by
    simpa [prefixWord, tailWord_787920, baseEnd_787920] using wordTrace_append hprefix tailTrace_787920
  have hstable : (prefixWord ++ tailWord_787920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787920).length < 2 ^ (prefixWord ++ tailWord_787920).sum := by decide
  have hdescent : baseEnd_787920 < baseStart_787920 := by decide
  rcases family_descends (prefixWord ++ tailWord_787920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787939 : List Nat := [1, 1, 1, 6, 2, 1, 1, 3, 3, 3]
def baseStart_787939 : Nat := 118140960795 + 787939 * 2 ^ 59
def prefixEnd_787939 : Nat := 4983230072969 + 3 ^ 40 * 787939 * 2
def baseEnd_787939 : Nat := 269727622282065279159227

theorem tailTrace_787939 : CollatzResearch.WordTrace tailWord_787939 prefixEnd_787939 269727622282065279159227 := by
  unfold tailWord_787939
  simp only [CollatzResearch.WordTrace]
  refine ⟨28738496292439047112702871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19158997528292698075135247 28738496292439047112702871)
  ·
    refine ⟨43107744438658570669054307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28738496292439047112702871 43107744438658570669054307)
    ·
      refine ⟨64661616657987856003581461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43107744438658570669054307 64661616657987856003581461)
      ·
        refine ⟨3031013280843180750167881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 64661616657987856003581461 3031013280843180750167881)
        ·
          refine ⟨2273259960632385562625911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3031013280843180750167881 2273259960632385562625911)
          ·
            refine ⟨3409889940948578343938867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2273259960632385562625911 3409889940948578343938867)
            ·
              refine ⟨5114834911422867515908301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3409889940948578343938867 5114834911422867515908301)
              ·
                refine ⟨1918063091783575318465613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5114834911422867515908301 1918063091783575318465613)
                ·
                  refine ⟨719273659418840744424605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1918063091783575318465613 719273659418840744424605)
                  ·
                    refine ⟨269727622282065279159227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 719273659418840744424605 269727622282065279159227)
                    ·
                      rfl

theorem cell22_787939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 3, 3].length) (baseStart_787939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_787939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_787939 prefixEnd_787939 := by exact prefixLift 787939
  have htrace : WordTrace (prefixWord ++ tailWord_787939) baseStart_787939 baseEnd_787939 := by
    simpa [prefixWord, tailWord_787939, baseEnd_787939] using wordTrace_append hprefix tailTrace_787939
  have hstable : (prefixWord ++ tailWord_787939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787939).length < 2 ^ (prefixWord ++ tailWord_787939).sum := by decide
  have hdescent : baseEnd_787939 < baseStart_787939 := by decide
  rcases family_descends (prefixWord ++ tailWord_787939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788003 : List Nat := [1, 1, 1, 4, 6, 1, 2, 1, 5]
def baseStart_788003 : Nat := 118140960795 + 788003 * 2 ^ 59
def prefixEnd_788003 : Nat := 4983230072969 + 3 ^ 40 * 788003 * 2
def baseEnd_788003 : Nat := 89916510263330148519677

theorem tailTrace_788003 : CollatzResearch.WordTrace tailWord_788003 prefixEnd_788003 89916510263330148519677 := by
  unfold tailWord_788003
  simp only [CollatzResearch.WordTrace]
  refine ⟨28740830564207186043032663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19160553709471457362021775 28740830564207186043032663)
  ·
    refine ⟨43111245846310779064548995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28740830564207186043032663 43111245846310779064548995)
    ·
      refine ⟨64666868769466168596823493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43111245846310779064548995 64666868769466168596823493)
      ·
        refine ⟨12125037894274906611904405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64666868769466168596823493 12125037894274906611904405)
        ·
          refine ⟨568361151294136247433019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12125037894274906611904405 568361151294136247433019)
          ·
            refine ⟨852541726941204371149529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 568361151294136247433019 852541726941204371149529)
            ·
              refine ⟨639406295205903278362147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 852541726941204371149529 639406295205903278362147)
              ·
                refine ⟨959109442808854917543221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 639406295205903278362147 959109442808854917543221)
                ·
                  refine ⟨89916510263330148519677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 959109442808854917543221 89916510263330148519677)
                  ·
                    rfl

theorem cell22_788003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 1, 5].length) (baseStart_788003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_788003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_788003 prefixEnd_788003 := by exact prefixLift 788003
  have htrace : WordTrace (prefixWord ++ tailWord_788003) baseStart_788003 baseEnd_788003 := by
    simpa [prefixWord, tailWord_788003, baseEnd_788003] using wordTrace_append hprefix tailTrace_788003
  have hstable : (prefixWord ++ tailWord_788003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788003).length < 2 ^ (prefixWord ++ tailWord_788003).sum := by decide
  have hdescent : baseEnd_788003 < baseStart_788003 := by decide
  rcases family_descends (prefixWord ++ tailWord_788003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788044 : List Nat := [2, 2, 1, 3, 1, 3, 2, 2, 2, 4]
def baseStart_788044 : Nat := 118140960795 + 788044 * 2 ^ 59
def prefixEnd_788044 : Nat := 4983230072969 + 3 ^ 40 * 788044 * 2
def baseEnd_788044 : Nat := 269763565927880005283905

theorem tailTrace_788044 : CollatzResearch.WordTrace tailWord_788044 prefixEnd_788044 269763565927880005283905 := by
  unfold tailWord_788044
  simp only [CollatzResearch.WordTrace]
  refine ⟨14371162978529325022637593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19161550638039100030183457 14371162978529325022637593)
  ·
    refine ⟨10778372233896993766978195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14371162978529325022637593 10778372233896993766978195)
    ·
      refine ⟨16167558350845490650467293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10778372233896993766978195 16167558350845490650467293)
      ·
        refine ⟨6062834381567058993925235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16167558350845490650467293 6062834381567058993925235)
        ·
          refine ⟨9094251572350588490887853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6062834381567058993925235 9094251572350588490887853)
          ·
            refine ⟨3410344339631470684082945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9094251572350588490887853 3410344339631470684082945)
            ·
              refine ⟨2557758254723603013062209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3410344339631470684082945 2557758254723603013062209)
              ·
                refine ⟨1918318691042702259796657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2557758254723603013062209 1918318691042702259796657)
                ·
                  refine ⟨1438739018282026694847493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1918318691042702259796657 1438739018282026694847493)
                  ·
                    refine ⟨269763565927880005283905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1438739018282026694847493 269763565927880005283905)
                    ·
                      rfl

theorem cell22_788044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 2, 4].length) (baseStart_788044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_788044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_788044 prefixEnd_788044 := by exact prefixLift 788044
  have htrace : WordTrace (prefixWord ++ tailWord_788044) baseStart_788044 baseEnd_788044 := by
    simpa [prefixWord, tailWord_788044, baseEnd_788044] using wordTrace_append hprefix tailTrace_788044
  have hstable : (prefixWord ++ tailWord_788044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788044).length < 2 ^ (prefixWord ++ tailWord_788044).sum := by decide
  have hdescent : baseEnd_788044 < baseStart_788044 := by decide
  rcases family_descends (prefixWord ++ tailWord_788044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788078 : List Nat := [4, 1, 2, 2, 3, 2, 1, 1, 2, 4]
def baseStart_788078 : Nat := 118140960795 + 788078 * 2 ^ 59
def prefixEnd_788078 : Nat := 4983230072969 + 3 ^ 40 * 788078 * 2
def baseEnd_788078 : Nat := 269775204822715249933801

theorem tailTrace_788078 : CollatzResearch.WordTrace tailWord_788078 prefixEnd_788078 269775204822715249933801 := by
  unfold tailWord_788078
  simp only [CollatzResearch.WordTrace]
  refine ⟨3592945754866934231501611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19162377359290315901341925 3592945754866934231501611)
  ·
    refine ⟨5389418632300401347252417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3592945754866934231501611 5389418632300401347252417)
    ·
      refine ⟨4042063974225301010439313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5389418632300401347252417 4042063974225301010439313)
      ·
        refine ⟨3031547980668975757829485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4042063974225301010439313 3031547980668975757829485)
        ·
          refine ⟨1136830492750865909186057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3031547980668975757829485 1136830492750865909186057)
          ·
            refine ⟨852622869563149431889543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1136830492750865909186057 852622869563149431889543)
            ·
              refine ⟨1278934304344724147834315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 852622869563149431889543 1278934304344724147834315)
              ·
                refine ⟨1918401456517086221751473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1278934304344724147834315 1918401456517086221751473)
                ·
                  refine ⟨1438801092387814666313605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1918401456517086221751473 1438801092387814666313605)
                  ·
                    refine ⟨269775204822715249933801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1438801092387814666313605 269775204822715249933801)
                    ·
                      rfl

theorem cell22_788078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_788078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_788078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_788078 prefixEnd_788078 := by exact prefixLift 788078
  have htrace : WordTrace (prefixWord ++ tailWord_788078) baseStart_788078 baseEnd_788078 := by
    simpa [prefixWord, tailWord_788078, baseEnd_788078] using wordTrace_append hprefix tailTrace_788078
  have hstable : (prefixWord ++ tailWord_788078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788078).length < 2 ^ (prefixWord ++ tailWord_788078).sum := by decide
  have hdescent : baseEnd_788078 < baseStart_788078 := by decide
  rcases family_descends (prefixWord ++ tailWord_788078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788087 : List Nat := [1, 1, 3, 1, 1, 3, 1, 4, 7]
def baseStart_788087 : Nat := 118140960795 + 788087 * 2 ^ 59
def prefixEnd_788087 : Nat := 4983230072969 + 3 ^ 40 * 788087 * 2
def baseEnd_788087 : Nat := 89926095235547408819591

theorem tailTrace_788087 : CollatzResearch.WordTrace tailWord_788087 prefixEnd_788087 89926095235547408819591 := by
  unfold tailWord_788087
  simp only [CollatzResearch.WordTrace]
  refine ⟨28743894295902868389090515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19162596197268578926060343 28743894295902868389090515)
  ·
    refine ⟨43115841443854302583635773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28743894295902868389090515 43115841443854302583635773)
    ·
      refine ⟨16168440541445363468863415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43115841443854302583635773 16168440541445363468863415)
      ·
        refine ⟨24252660812168045203295123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16168440541445363468863415 24252660812168045203295123)
        ·
          refine ⟨36378991218252067804942685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24252660812168045203295123 36378991218252067804942685)
          ·
            refine ⟨13642121706844525426853507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36378991218252067804942685 13642121706844525426853507)
            ·
              refine ⟨20463182560266788140280261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13642121706844525426853507 20463182560266788140280261)
              ·
                refine ⟨3836846730050022776302549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20463182560266788140280261 3836846730050022776302549)
                ·
                  refine ⟨89926095235547408819591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3836846730050022776302549 89926095235547408819591)
                  ·
                    rfl

theorem cell22_788087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 7].length) (baseStart_788087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_788087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_788087 prefixEnd_788087 := by exact prefixLift 788087
  have htrace : WordTrace (prefixWord ++ tailWord_788087) baseStart_788087 baseEnd_788087 := by
    simpa [prefixWord, tailWord_788087, baseEnd_788087] using wordTrace_append hprefix tailTrace_788087
  have hstable : (prefixWord ++ tailWord_788087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788087).length < 2 ^ (prefixWord ++ tailWord_788087).sum := by decide
  have hdescent : baseEnd_788087 < baseStart_788087 := by decide
  rcases family_descends (prefixWord ++ tailWord_788087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788119 : List Nat := [1, 1, 3, 3, 2, 2, 2, 1, 2, 5]
def baseStart_788119 : Nat := 118140960795 + 788119 * 2 ^ 59
def prefixEnd_788119 : Nat := 4983230072969 + 3 ^ 40 * 788119 * 2
def baseEnd_788119 : Nat := 269789239960604809658675

theorem tailTrace_788119 : CollatzResearch.WordTrace tailWord_788119 prefixEnd_788119 269789239960604809658675 := by
  unfold tailWord_788119
  simp only [CollatzResearch.WordTrace]
  refine ⟨28745061431786937854255411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19163374287857958569503607 28745061431786937854255411)
  ·
    refine ⟨43117592147680406781383117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28745061431786937854255411 43117592147680406781383117)
    ·
      refine ⟨16169097055380152543018669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43117592147680406781383117 16169097055380152543018669)
      ·
        refine ⟨6063411395767557203632001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16169097055380152543018669 6063411395767557203632001)
        ·
          refine ⟨4547558546825667902724001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6063411395767557203632001 4547558546825667902724001)
          ·
            refine ⟨3410668910119250927043001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4547558546825667902724001 3410668910119250927043001)
            ·
              refine ⟨2558001682589438195282251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3410668910119250927043001 2558001682589438195282251)
              ·
                refine ⟨3837002523884157292923377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2558001682589438195282251 3837002523884157292923377)
                ·
                  refine ⟨2877751892913117969692533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3837002523884157292923377 2877751892913117969692533)
                  ·
                    refine ⟨269789239960604809658675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2877751892913117969692533 269789239960604809658675)
                    ·
                      rfl

theorem cell22_788119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 5].length) (baseStart_788119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_788119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_788119 prefixEnd_788119 := by exact prefixLift 788119
  have htrace : WordTrace (prefixWord ++ tailWord_788119) baseStart_788119 baseEnd_788119 := by
    simpa [prefixWord, tailWord_788119, baseEnd_788119] using wordTrace_append hprefix tailTrace_788119
  have hstable : (prefixWord ++ tailWord_788119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788119).length < 2 ^ (prefixWord ++ tailWord_788119).sum := by decide
  have hdescent : baseEnd_788119 < baseStart_788119 := by decide
  rcases family_descends (prefixWord ++ tailWord_788119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788151 : List Nat := [1, 1, 3, 1, 5, 1, 2, 3, 1, 4]
def baseStart_788151 : Nat := 118140960795 + 788151 * 2 ^ 59
def prefixEnd_788151 : Nat := 4983230072969 + 3 ^ 40 * 788151 * 2
def baseEnd_788151 : Nat := 269800194214567392858577

theorem tailTrace_788151 : CollatzResearch.WordTrace tailWord_788151 prefixEnd_788151 269800194214567392858577 := by
  unfold tailWord_788151
  simp only [CollatzResearch.WordTrace]
  refine ⟨28746228567671007319420307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19164152378447338212946871 28746228567671007319420307)
  ·
    refine ⟨43119342851506510979130461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28746228567671007319420307 43119342851506510979130461)
    ·
      refine ⟨16169753569314941617173923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43119342851506510979130461 16169753569314941617173923)
      ·
        refine ⟨24254630353972412425760885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16169753569314941617173923 24254630353972412425760885)
        ·
          refine ⟨2273871595684913664915083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24254630353972412425760885 2273871595684913664915083)
          ·
            refine ⟨3410807393527370497372625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2273871595684913664915083 3410807393527370497372625)
            ·
              refine ⟨2558105545145527873029469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3410807393527370497372625 2558105545145527873029469)
              ·
                refine ⟨959289579429572952386051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2558105545145527873029469 959289579429572952386051)
                ·
                  refine ⟨1438934369144359428579077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 959289579429572952386051 1438934369144359428579077)
                  ·
                    refine ⟨269800194214567392858577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1438934369144359428579077 269800194214567392858577)
                    ·
                      rfl

theorem cell22_788151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 3, 1, 4].length) (baseStart_788151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_788151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_788151 prefixEnd_788151 := by exact prefixLift 788151
  have htrace : WordTrace (prefixWord ++ tailWord_788151) baseStart_788151 baseEnd_788151 := by
    simpa [prefixWord, tailWord_788151, baseEnd_788151] using wordTrace_append hprefix tailTrace_788151
  have hstable : (prefixWord ++ tailWord_788151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788151).length < 2 ^ (prefixWord ++ tailWord_788151).sum := by decide
  have hdescent : baseEnd_788151 < baseStart_788151 := by decide
  rcases family_descends (prefixWord ++ tailWord_788151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788196 : List Nat := [2, 3, 1, 1, 1, 3, 4, 1, 2, 4]
def baseStart_788196 : Nat := 118140960795 + 788196 * 2 ^ 59
def prefixEnd_788196 : Nat := 4983230072969 + 3 ^ 40 * 788196 * 2
def baseEnd_788196 : Nat := 269815598634202275483439

theorem tailTrace_788196 : CollatzResearch.WordTrace tailWord_788196 prefixEnd_788196 269815598634202275483439 := by
  unfold tailWord_788196
  simp only [CollatzResearch.WordTrace]
  refine ⟨14373934926253990002404221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19165246568338653336538961 14373934926253990002404221)
  ·
    refine ⟨5390225597345246250901583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14373934926253990002404221 5390225597345246250901583)
    ·
      refine ⟨8085338396017869376352375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5390225597345246250901583 8085338396017869376352375)
      ·
        refine ⟨12128007594026804064528563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8085338396017869376352375 12128007594026804064528563)
        ·
          refine ⟨18192011391040206096792845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12128007594026804064528563 18192011391040206096792845)
          ·
            refine ⟨6822004271640077286297317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18192011391040206096792845 6822004271640077286297317)
            ·
              refine ⟨1279125800932514491180747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6822004271640077286297317 1279125800932514491180747)
              ·
                refine ⟨1918688701398771736771121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1279125800932514491180747 1918688701398771736771121)
                ·
                  refine ⟨1439016526049078802578341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1918688701398771736771121 1439016526049078802578341)
                  ·
                    refine ⟨269815598634202275483439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1439016526049078802578341 269815598634202275483439)
                    ·
                      rfl

theorem cell22_788196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_788196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_788196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_788196 prefixEnd_788196 := by exact prefixLift 788196
  have htrace : WordTrace (prefixWord ++ tailWord_788196) baseStart_788196 baseEnd_788196 := by
    simpa [prefixWord, tailWord_788196, baseEnd_788196] using wordTrace_append hprefix tailTrace_788196
  have hstable : (prefixWord ++ tailWord_788196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788196).length < 2 ^ (prefixWord ++ tailWord_788196).sum := by decide
  have hdescent : baseEnd_788196 < baseStart_788196 := by decide
  rcases family_descends (prefixWord ++ tailWord_788196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788260 : List Nat := [2, 3, 1, 3, 2, 1, 1, 5, 1, 3]
def baseStart_788260 : Nat := 118140960795 + 788260 * 2 ^ 59
def prefixEnd_788260 : Nat := 4983230072969 + 3 ^ 40 * 788260 * 2
def baseEnd_788260 : Nat := 269837507142127441883243

theorem tailTrace_788260 : CollatzResearch.WordTrace tailWord_788260 prefixEnd_788260 269837507142127441883243 := by
  unfold tailWord_788260
  simp only [CollatzResearch.WordTrace]
  refine ⟨14375102062138059467569117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19166802749517412623425489 14375102062138059467569117)
  ·
    refine ⟨5390663273301772300338419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14375102062138059467569117 5390663273301772300338419)
    ·
      refine ⟨8085994909952658450507629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5390663273301772300338419 8085994909952658450507629)
      ·
        refine ⟨3032248091232246918940361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8085994909952658450507629 3032248091232246918940361)
        ·
          refine ⟨2274186068424185189205271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3032248091232246918940361 2274186068424185189205271)
          ·
            refine ⟨3411279102636277783807907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2274186068424185189205271 3411279102636277783807907)
            ·
              refine ⟨5116918653954416675711861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3411279102636277783807907 5116918653954416675711861)
              ·
                refine ⟨479711123808226563347987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5116918653954416675711861 479711123808226563347987)
                ·
                  refine ⟨719566685712339845021981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 479711123808226563347987 719566685712339845021981)
                  ·
                    refine ⟨269837507142127441883243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 719566685712339845021981 269837507142127441883243)
                    ·
                      rfl

theorem cell22_788260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 5, 1, 3].length) (baseStart_788260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_788260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_788260 prefixEnd_788260 := by exact prefixLift 788260
  have htrace : WordTrace (prefixWord ++ tailWord_788260) baseStart_788260 baseEnd_788260 := by
    simpa [prefixWord, tailWord_788260, baseEnd_788260] using wordTrace_append hprefix tailTrace_788260
  have hstable : (prefixWord ++ tailWord_788260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788260).length < 2 ^ (prefixWord ++ tailWord_788260).sum := by decide
  have hdescent : baseEnd_788260 < baseStart_788260 := by decide
  rcases family_descends (prefixWord ++ tailWord_788260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788273 : List Nat := [1, 2, 2, 3, 2, 4, 1, 2, 5]
def baseStart_788273 : Nat := 118140960795 + 788273 * 2 ^ 59
def prefixEnd_788273 : Nat := 4983230072969 + 3 ^ 40 * 788273 * 2
def baseEnd_788273 : Nat := 89947319102599913769401

theorem tailTrace_788273 : CollatzResearch.WordTrace tailWord_788273 prefixEnd_788273 89947319102599913769401 := by
  unfold tailWord_788273
  simp only [CollatzResearch.WordTrace]
  refine ⟨28750678273229022155361473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19167118848819348103574315 28750678273229022155361473)
  ·
    refine ⟨21563008704921766616521105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28750678273229022155361473 21563008704921766616521105)
    ·
      refine ⟨16172256528691324962390829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21563008704921766616521105 16172256528691324962390829)
      ·
        refine ⟨6064596198259246860896561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16172256528691324962390829 6064596198259246860896561)
        ·
          refine ⟨4548447148694435145672421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6064596198259246860896561 4548447148694435145672421)
          ·
            refine ⟨852833840380206589813579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4548447148694435145672421 852833840380206589813579)
            ·
              refine ⟨1279250760570309884720369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 852833840380206589813579 1279250760570309884720369)
              ·
                refine ⟨959438070427732413540277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1279250760570309884720369 959438070427732413540277)
                ·
                  refine ⟨89947319102599913769401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 959438070427732413540277 89947319102599913769401)
                  ·
                    rfl

theorem cell22_788273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 2, 5].length) (baseStart_788273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_788273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_788273 prefixEnd_788273 := by exact prefixLift 788273
  have htrace : WordTrace (prefixWord ++ tailWord_788273) baseStart_788273 baseEnd_788273 := by
    simpa [prefixWord, tailWord_788273, baseEnd_788273] using wordTrace_append hprefix tailTrace_788273
  have hstable : (prefixWord ++ tailWord_788273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788273).length < 2 ^ (prefixWord ++ tailWord_788273).sum := by decide
  have hdescent : baseEnd_788273 < baseStart_788273 := by decide
  rcases family_descends (prefixWord ++ tailWord_788273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788333 : List Nat := [1, 5, 1, 1, 1, 1, 4, 1, 4, 3]
def baseStart_788333 : Nat := 118140960795 + 788333 * 2 ^ 59
def prefixEnd_788333 : Nat := 4983230072969 + 3 ^ 40 * 788333 * 2
def baseEnd_788333 : Nat := 269862496533979584808019

theorem tailTrace_788333 : CollatzResearch.WordTrace tailWord_788333 prefixEnd_788333 269862496533979584808019 := by
  unfold tailWord_788333
  simp only [CollatzResearch.WordTrace]
  refine ⟨28752866653011652402545653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19168577768674434935030435 28752866653011652402545653)
  ·
    refine ⟨2695581248719842412738655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28752866653011652402545653 2695581248719842412738655)
    ·
      refine ⟨4043371873079763619107983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2695581248719842412738655 4043371873079763619107983)
      ·
        refine ⟨6065057809619645428661975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4043371873079763619107983 6065057809619645428661975)
        ·
          refine ⟨9097586714429468142992963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6065057809619645428661975 9097586714429468142992963)
          ·
            refine ⟨13646380071644202214489445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9097586714429468142992963 13646380071644202214489445)
            ·
              refine ⟨2558696263433287915216771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13646380071644202214489445 2558696263433287915216771)
              ·
                refine ⟨3838044395149931872825157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2558696263433287915216771 3838044395149931872825157)
                ·
                  refine ⟨719633324090612226154717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3838044395149931872825157 719633324090612226154717)
                  ·
                    refine ⟨269862496533979584808019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 719633324090612226154717 269862496533979584808019)
                    ·
                      rfl

theorem cell22_788333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_788333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_788333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_788333 prefixEnd_788333 := by exact prefixLift 788333
  have htrace : WordTrace (prefixWord ++ tailWord_788333) baseStart_788333 baseEnd_788333 := by
    simpa [prefixWord, tailWord_788333, baseEnd_788333] using wordTrace_append hprefix tailTrace_788333
  have hstable : (prefixWord ++ tailWord_788333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788333).length < 2 ^ (prefixWord ++ tailWord_788333).sum := by decide
  have hdescent : baseEnd_788333 < baseStart_788333 := by decide
  rcases family_descends (prefixWord ++ tailWord_788333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788412 : List Nat := [2, 2, 2, 5, 1, 1, 1, 2, 3, 3]
def baseStart_788412 : Nat := 118140960795 + 788412 * 2 ^ 59
def prefixEnd_788412 : Nat := 4983230072969 + 3 ^ 40 * 788412 * 2
def baseEnd_788412 : Nat := 269889539848449712082777

theorem tailTrace_788412 : CollatzResearch.WordTrace tailWord_788412 prefixEnd_788412 269889539848449712082777 := by
  unfold tailWord_788412
  simp only [CollatzResearch.WordTrace]
  refine ⟨14377874009862724447335745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19170498679816965929780993 14377874009862724447335745)
  ·
    refine ⟨10783405507397043335501809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14377874009862724447335745 10783405507397043335501809)
    ·
      refine ⟨8087554130547782501626357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10783405507397043335501809 8087554130547782501626357)
      ·
        refine ⟨758208199738854609527471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8087554130547782501626357 758208199738854609527471)
        ·
          refine ⟨1137312299608281914291207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 758208199738854609527471 1137312299608281914291207)
          ·
            refine ⟨1705968449412422871436811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1137312299608281914291207 1705968449412422871436811)
            ·
              refine ⟨2558952674118634307155217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1705968449412422871436811 2558952674118634307155217)
              ·
                refine ⟨1919214505588975730366413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2558952674118634307155217 1919214505588975730366413)
                ·
                  refine ⟨719705439595865898887405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1919214505588975730366413 719705439595865898887405)
                  ·
                    refine ⟨269889539848449712082777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 719705439595865898887405 269889539848449712082777)
                    ·
                      rfl

theorem cell22_788412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 3, 3].length) (baseStart_788412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_788412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_788412 prefixEnd_788412 := by exact prefixLift 788412
  have htrace : WordTrace (prefixWord ++ tailWord_788412) baseStart_788412 baseEnd_788412 := by
    simpa [prefixWord, tailWord_788412, baseEnd_788412] using wordTrace_append hprefix tailTrace_788412
  have hstable : (prefixWord ++ tailWord_788412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788412).length < 2 ^ (prefixWord ++ tailWord_788412).sum := by decide
  have hdescent : baseEnd_788412 < baseStart_788412 := by decide
  rcases family_descends (prefixWord ++ tailWord_788412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788442 : List Nat := [3, 1, 1, 2, 6, 1, 1, 2, 5]
def baseStart_788442 : Nat := 118140960795 + 788442 * 2 ^ 59
def prefixEnd_788442 : Nat := 4983230072969 + 3 ^ 40 * 788442 * 2
def baseEnd_788442 : Nat := 89966603153846544610895

theorem tailTrace_788442 : CollatzResearch.WordTrace tailWord_788442 prefixEnd_788442 89966603153846544610895 := by
  unfold tailWord_788442
  simp only [CollatzResearch.WordTrace]
  refine ⟨7189210552404191004565895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19171228139744509345509053 7189210552404191004565895)
  ·
    refine ⟨10783815828606286506848843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7189210552404191004565895 10783815828606286506848843)
    ·
      refine ⟨16175723742909429760273265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10783815828606286506848843 16175723742909429760273265)
      ·
        refine ⟨12131792807182072320204949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16175723742909429760273265 12131792807182072320204949)
        ·
          refine ⟨568677787836659640009607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12131792807182072320204949 568677787836659640009607)
          ·
            refine ⟨853016681754989460014411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 568677787836659640009607 853016681754989460014411)
            ·
              refine ⟨1279525022632484190021617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 853016681754989460014411 1279525022632484190021617)
              ·
                refine ⟨959643766974363142516213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1279525022632484190021617 959643766974363142516213)
                ·
                  refine ⟨89966603153846544610895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 959643766974363142516213 89966603153846544610895)
                  ·
                    rfl

theorem cell22_788442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 2, 5].length) (baseStart_788442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_788442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_788442 prefixEnd_788442 := by exact prefixLift 788442
  have htrace : WordTrace (prefixWord ++ tailWord_788442) baseStart_788442 baseEnd_788442 := by
    simpa [prefixWord, tailWord_788442, baseEnd_788442] using wordTrace_append hprefix tailTrace_788442
  have hstable : (prefixWord ++ tailWord_788442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788442).length < 2 ^ (prefixWord ++ tailWord_788442).sum := by decide
  have hdescent : baseEnd_788442 < baseStart_788442 := by decide
  rcases family_descends (prefixWord ++ tailWord_788442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788487 : List Nat := [1, 1, 4, 3, 1, 4, 1, 3, 4]
def baseStart_788487 : Nat := 118140960795 + 788487 * 2 ^ 59
def prefixEnd_788487 : Nat := 4983230072969 + 3 ^ 40 * 788487 * 2
def baseEnd_788487 : Nat := 89971737960391505485849

theorem tailTrace_788487 : CollatzResearch.WordTrace tailWord_788487 prefixEnd_788487 89971737960391505485849 := by
  unfold tailWord_788487
  simp only [CollatzResearch.WordTrace]
  refine ⟨28758483494453736703651715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19172322329635824469101143 28758483494453736703651715)
  ·
    refine ⟨43137725241680605055477573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28758483494453736703651715 43137725241680605055477573)
    ·
      refine ⟨8088323482815113447902045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43137725241680605055477573 8088323482815113447902045)
      ·
        refine ⟨3033121306055667542963267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8088323482815113447902045 3033121306055667542963267)
        ·
          refine ⟨4549681959083501314444901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3033121306055667542963267 4549681959083501314444901)
          ·
            refine ⟨853065367328156496458419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4549681959083501314444901 853065367328156496458419)
            ·
              refine ⟨1279598050992234744687629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 853065367328156496458419 1279598050992234744687629)
              ·
                refine ⟨479849269122088029257861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1279598050992234744687629 479849269122088029257861)
                ·
                  refine ⟨89971737960391505485849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 479849269122088029257861 89971737960391505485849)
                  ·
                    rfl

theorem cell22_788487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 3, 4].length) (baseStart_788487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_788487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_788487 prefixEnd_788487 := by exact prefixLift 788487
  have htrace : WordTrace (prefixWord ++ tailWord_788487) baseStart_788487 baseEnd_788487 := by
    simpa [prefixWord, tailWord_788487, baseEnd_788487] using wordTrace_append hprefix tailTrace_788487
  have hstable : (prefixWord ++ tailWord_788487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788487).length < 2 ^ (prefixWord ++ tailWord_788487).sum := by decide
  have hdescent : baseEnd_788487 < baseStart_788487 := by decide
  rcases family_descends (prefixWord ++ tailWord_788487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788496 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 1, 9]
def baseStart_788496 : Nat := 118140960795 + 788496 * 2 ^ 59
def prefixEnd_788496 : Nat := 4983230072969 + 3 ^ 40 * 788496 * 2
def baseEnd_788496 : Nat := 269918294765101492982519

theorem tailTrace_788496 : CollatzResearch.WordTrace tailWord_788496 prefixEnd_788496 269918294765101492982519 := by
  unfold tailWord_788496
  simp only [CollatzResearch.WordTrace]
  refine ⟨14379405875710565620364671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19172541167614087493819561 14379405875710565620364671)
  ·
    refine ⟨21569108813565848430547007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14379405875710565620364671 21569108813565848430547007)
    ·
      refine ⟨32353663220348772645820511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21569108813565848430547007 32353663220348772645820511)
      ·
        refine ⟨48530494830523158968730767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32353663220348772645820511 48530494830523158968730767)
        ·
          refine ⟨72795742245784738453096151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48530494830523158968730767 72795742245784738453096151)
          ·
            refine ⟨109193613368677107679644227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72795742245784738453096151 109193613368677107679644227)
            ·
              refine ⟨163790420053015661519466341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109193613368677107679644227 163790420053015661519466341)
              ·
                refine ⟨30710703759940436534899939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163790420053015661519466341 30710703759940436534899939)
                ·
                  refine ⟨46066055639910654802349909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30710703759940436534899939 46066055639910654802349909)
                  ·
                    refine ⟨269918294765101492982519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 46066055639910654802349909 269918294765101492982519)
                    ·
                      rfl

theorem cell22_788496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 1, 9].length) (baseStart_788496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_788496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_788496 prefixEnd_788496 := by exact prefixLift 788496
  have htrace : WordTrace (prefixWord ++ tailWord_788496) baseStart_788496 baseEnd_788496 := by
    simpa [prefixWord, tailWord_788496, baseEnd_788496] using wordTrace_append hprefix tailTrace_788496
  have hstable : (prefixWord ++ tailWord_788496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788496).length < 2 ^ (prefixWord ++ tailWord_788496).sum := by decide
  have hdescent : baseEnd_788496 < baseStart_788496 := by decide
  rcases family_descends (prefixWord ++ tailWord_788496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788519 : List Nat := [1, 1, 7, 1, 2, 1, 1, 3, 2, 3]
def baseStart_788519 : Nat := 118140960795 + 788519 * 2 ^ 59
def prefixEnd_788519 : Nat := 4983230072969 + 3 ^ 40 * 788519 * 2
def baseEnd_788519 : Nat := 269926168135137099657449

theorem tailTrace_788519 : CollatzResearch.WordTrace tailWord_788519 prefixEnd_788519 269926168135137099657449 := by
  unfold tailWord_788519
  simp only [CollatzResearch.WordTrace]
  refine ⟨28759650630337806168816611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19173100420225204112544407 28759650630337806168816611)
  ·
    refine ⟨43139475945506709253224917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28759650630337806168816611 43139475945506709253224917)
    ·
      refine ⟨1011081467472813498122459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 43139475945506709253224917 1011081467472813498122459)
      ·
        refine ⟨1516622201209220247183689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1011081467472813498122459 1516622201209220247183689)
        ·
          refine ⟨1137466650906915185387767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1516622201209220247183689 1137466650906915185387767)
          ·
            refine ⟨1706199976360372778081651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1137466650906915185387767 1706199976360372778081651)
            ·
              refine ⟨2559299964540559167122477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1706199976360372778081651 2559299964540559167122477)
              ·
                refine ⟨959737486702709687670929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2559299964540559167122477 959737486702709687670929)
                ·
                  refine ⟨719803115027032265753197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 959737486702709687670929 719803115027032265753197)
                  ·
                    refine ⟨269926168135137099657449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 719803115027032265753197 269926168135137099657449)
                    ·
                      rfl

theorem cell22_788519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_788519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_788519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_788519 prefixEnd_788519 := by exact prefixLift 788519
  have htrace : WordTrace (prefixWord ++ tailWord_788519) baseStart_788519 baseEnd_788519 := by
    simpa [prefixWord, tailWord_788519, baseEnd_788519] using wordTrace_append hprefix tailTrace_788519
  have hstable : (prefixWord ++ tailWord_788519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788519).length < 2 ^ (prefixWord ++ tailWord_788519).sum := by decide
  have hdescent : baseEnd_788519 < baseStart_788519 := by decide
  rcases family_descends (prefixWord ++ tailWord_788519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788588 : List Nat := [2, 2, 1, 1, 3, 3, 1, 1, 8]
def baseStart_788588 : Nat := 118140960795 + 788588 * 2 ^ 59
def prefixEnd_788588 : Nat := 4983230072969 + 3 ^ 40 * 788588 * 2
def baseEnd_788588 : Nat := 89983262748414639894079

theorem tailTrace_788588 : CollatzResearch.WordTrace tailWord_788588 prefixEnd_788588 89983262748414639894079 := by
  unfold tailWord_788588
  simp only [CollatzResearch.WordTrace]
  refine ⟨14381083633543915476539209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19174778178058553968718945 14381083633543915476539209)
  ·
    refine ⟨10785812725157936607404407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14381083633543915476539209 10785812725157936607404407)
    ·
      refine ⟨16178719087736904911106611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10785812725157936607404407 16178719087736904911106611)
      ·
        refine ⟨24268078631605357366659917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16178719087736904911106611 24268078631605357366659917)
        ·
          refine ⟨9100529486852009012497469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24268078631605357366659917 9100529486852009012497469)
          ·
            refine ⟨3412698557569503379686551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9100529486852009012497469 3412698557569503379686551)
            ·
              refine ⟨5119047836354255069529827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3412698557569503379686551 5119047836354255069529827)
              ·
                refine ⟨7678571754531382604294741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5119047836354255069529827 7678571754531382604294741)
                ·
                  refine ⟨89983262748414639894079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7678571754531382604294741 89983262748414639894079)
                  ·
                    rfl

theorem cell22_788588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 8].length) (baseStart_788588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_788588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_788588 prefixEnd_788588 := by exact prefixLift 788588
  have htrace : WordTrace (prefixWord ++ tailWord_788588) baseStart_788588 baseEnd_788588 := by
    simpa [prefixWord, tailWord_788588, baseEnd_788588] using wordTrace_append hprefix tailTrace_788588
  have hstable : (prefixWord ++ tailWord_788588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788588).length < 2 ^ (prefixWord ++ tailWord_788588).sum := by decide
  have hdescent : baseEnd_788588 < baseStart_788588 := by decide
  rcases family_descends (prefixWord ++ tailWord_788588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788590 : List Nat := [4, 1, 2, 2, 1, 1, 1, 3, 3, 4]
def baseStart_788590 : Nat := 118140960795 + 788590 * 2 ^ 59
def prefixEnd_788590 : Nat := 4983230072969 + 3 ^ 40 * 788590 * 2
def baseEnd_788590 : Nat := 269950472886116581132231

theorem tailTrace_788590 : CollatzResearch.WordTrace tailWord_788590 prefixEnd_788590 269950472886116581132231 := by
  unfold tailWord_788590
  simp only [CollatzResearch.WordTrace]
  refine ⟨3595280026635073161831403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19174826808720390196434149 3595280026635073161831403)
  ·
    refine ⟨5392920039952609742747105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3595280026635073161831403 5392920039952609742747105)
    ·
      refine ⟨4044690029964457307060329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5392920039952609742747105 4044690029964457307060329)
      ·
        refine ⟨3033517522473342980295247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4044690029964457307060329 3033517522473342980295247)
        ·
          refine ⟨4550276283710014470442871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3033517522473342980295247 4550276283710014470442871)
          ·
            refine ⟨6825414425565021705664307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4550276283710014470442871 6825414425565021705664307)
            ·
              refine ⟨10238121638347532558496461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6825414425565021705664307 10238121638347532558496461)
              ·
                refine ⟨3839295614380324709436173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10238121638347532558496461 3839295614380324709436173)
                ·
                  refine ⟨1439735855392621766038565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3839295614380324709436173 1439735855392621766038565)
                  ·
                    refine ⟨269950472886116581132231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1439735855392621766038565 269950472886116581132231)
                    ·
                      rfl

theorem cell22_788590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_788590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_788590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_788590 prefixEnd_788590 := by exact prefixLift 788590
  have htrace : WordTrace (prefixWord ++ tailWord_788590) baseStart_788590 baseEnd_788590 := by
    simpa [prefixWord, tailWord_788590, baseEnd_788590] using wordTrace_append hprefix tailTrace_788590
  have hstable : (prefixWord ++ tailWord_788590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788590).length < 2 ^ (prefixWord ++ tailWord_788590).sum := by decide
  have hdescent : baseEnd_788590 < baseStart_788590 := by decide
  rcases family_descends (prefixWord ++ tailWord_788590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788622 : List Nat := [4, 1, 1, 3, 3, 1, 2, 1, 6]
def baseStart_788622 : Nat := 118140960795 + 788622 * 2 ^ 59
def prefixEnd_788622 : Nat := 4983230072969 + 3 ^ 40 * 788622 * 2
def baseEnd_788622 : Nat := 89987142380026388110711

theorem tailTrace_788622 : CollatzResearch.WordTrace tailWord_788622 prefixEnd_788622 89987142380026388110711 := by
  unfold tailWord_788622
  simp only [CollatzResearch.WordTrace]
  refine ⟨3595425918620581844977015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19175604899309769839877413 3595425918620581844977015)
  ·
    refine ⟨5393138877930872767465523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3595425918620581844977015 5393138877930872767465523)
    ·
      refine ⟨8089708316896309151198285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5393138877930872767465523 8089708316896309151198285)
      ·
        refine ⟨3033640618836115931699357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8089708316896309151198285 3033640618836115931699357)
        ·
          refine ⟨1137615232063543474387259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3033640618836115931699357 1137615232063543474387259)
          ·
            refine ⟨1706422848095315211580889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1137615232063543474387259 1706422848095315211580889)
            ·
              refine ⟨1279817136071486408685667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1706422848095315211580889 1279817136071486408685667)
              ·
                refine ⟨1919725704107229613028501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1279817136071486408685667 1919725704107229613028501)
                ·
                  refine ⟨89987142380026388110711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1919725704107229613028501 89987142380026388110711)
                  ·
                    rfl

theorem cell22_788622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 6].length) (baseStart_788622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_788622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_788622 prefixEnd_788622 := by exact prefixLift 788622
  have htrace : WordTrace (prefixWord ++ tailWord_788622) baseStart_788622 baseEnd_788622 := by
    simpa [prefixWord, tailWord_788622, baseEnd_788622] using wordTrace_append hprefix tailTrace_788622
  have hstable : (prefixWord ++ tailWord_788622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788622).length < 2 ^ (prefixWord ++ tailWord_788622).sum := by decide
  have hdescent : baseEnd_788622 < baseStart_788622 := by decide
  rcases family_descends (prefixWord ++ tailWord_788622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788637 : List Nat := [1, 4, 2, 1, 1, 5, 1, 1, 1, 5]
def baseStart_788637 : Nat := 118140960795 + 788637 * 2 ^ 59
def prefixEnd_788637 : Nat := 4983230072969 + 3 ^ 40 * 788637 * 2
def baseEnd_788637 : Nat := 269966561946624125207087

theorem tailTrace_788637 : CollatzResearch.WordTrace tailWord_788637 prefixEnd_788637 269966561946624125207087 := by
  unfold tailWord_788637
  simp only [CollatzResearch.WordTrace]
  refine ⟨28763954443910312321612165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19175969629273541547741443 28763954443910312321612165)
  ·
    refine ⟨5393241458233183560302281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28763954443910312321612165 5393241458233183560302281)
    ·
      refine ⟨4044931093674887670226711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5393241458233183560302281 4044931093674887670226711)
      ·
        refine ⟨6067396640512331505340067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4044931093674887670226711 6067396640512331505340067)
        ·
          refine ⟨9101094960768497258010101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6067396640512331505340067 9101094960768497258010101)
          ·
            refine ⟨853227652572046617938447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9101094960768497258010101 853227652572046617938447)
            ·
              refine ⟨1279841478858069926907671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 853227652572046617938447 1279841478858069926907671)
              ·
                refine ⟨1919762218287104890361507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1279841478858069926907671 1919762218287104890361507)
                ·
                  refine ⟨2879643327430657335542261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1919762218287104890361507 2879643327430657335542261)
                  ·
                    refine ⟨269966561946624125207087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2879643327430657335542261 269966561946624125207087)
                    ·
                      rfl

theorem cell22_788637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_788637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_788637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_788637 prefixEnd_788637 := by exact prefixLift 788637
  have htrace : WordTrace (prefixWord ++ tailWord_788637) baseStart_788637 baseEnd_788637 := by
    simpa [prefixWord, tailWord_788637, baseEnd_788637] using wordTrace_append hprefix tailTrace_788637
  have hstable : (prefixWord ++ tailWord_788637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788637).length < 2 ^ (prefixWord ++ tailWord_788637).sum := by decide
  have hdescent : baseEnd_788637 < baseStart_788637 := by decide
  rcases family_descends (prefixWord ++ tailWord_788637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788772 : List Nat := [2, 3, 1, 3, 1, 2, 2, 2, 1, 5]
def baseStart_788772 : Nat := 118140960795 + 788772 * 2 ^ 59
def prefixEnd_788772 : Nat := 4983230072969 + 3 ^ 40 * 788772 * 2
def baseEnd_788772 : Nat := 270012775205528773081673

theorem tailTrace_788772 : CollatzResearch.WordTrace tailWord_788772 prefixEnd_788772 270012775205528773081673 := by
  unfold tailWord_788772
  simp only [CollatzResearch.WordTrace]
  refine ⟨14384439149210615188888285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19179252198947486918517713 14384439149210615188888285)
  ·
    refine ⟨5394164680953980695833107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14384439149210615188888285 5394164680953980695833107)
    ·
      refine ⟨8091247021430971043749661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5394164680953980695833107 8091247021430971043749661)
      ·
        refine ⟨3034217633036614141406123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8091247021430971043749661 3034217633036614141406123)
        ·
          refine ⟨4551326449554921212109185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3034217633036614141406123 4551326449554921212109185)
          ·
            refine ⟨3413494837166190909081889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4551326449554921212109185 3413494837166190909081889)
            ·
              refine ⟨2560121127874643181811417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3413494837166190909081889 2560121127874643181811417)
              ·
                refine ⟨1920090845905982386358563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2560121127874643181811417 1920090845905982386358563)
                ·
                  refine ⟨2880136268858973579537845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1920090845905982386358563 2880136268858973579537845)
                  ·
                    refine ⟨270012775205528773081673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2880136268858973579537845 270012775205528773081673)
                    ·
                      rfl

theorem cell22_788772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_788772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_788772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_788772 prefixEnd_788772 := by exact prefixLift 788772
  have htrace : WordTrace (prefixWord ++ tailWord_788772) baseStart_788772 baseEnd_788772 := by
    simpa [prefixWord, tailWord_788772, baseEnd_788772] using wordTrace_append hprefix tailTrace_788772
  have hstable : (prefixWord ++ tailWord_788772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788772).length < 2 ^ (prefixWord ++ tailWord_788772).sum := by decide
  have hdescent : baseEnd_788772 < baseStart_788772 := by decide
  rcases family_descends (prefixWord ++ tailWord_788772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788922 : List Nat := [3, 1, 1, 1, 2, 1, 1, 4, 4, 4]
def baseStart_788922 : Nat := 118140960795 + 788922 * 2 ^ 59
def prefixEnd_788922 : Nat := 4983230072969 + 3 ^ 40 * 788922 * 2
def baseEnd_788922 : Nat := 270064123270978381831213

theorem tailTrace_788922 : CollatzResearch.WordTrace tailWord_788922 prefixEnd_788922 270064123270978381831213 := by
  unfold tailWord_788922
  simp only [CollatzResearch.WordTrace]
  refine ⟨7193587311969451498934255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19182899498585203997158013 7193587311969451498934255)
  ·
    refine ⟨10790380967954177248401383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7193587311969451498934255 10790380967954177248401383)
    ·
      refine ⟨16185571451931265872602075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10790380967954177248401383 16185571451931265872602075)
      ·
        refine ⟨24278357177896898808903113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16185571451931265872602075 24278357177896898808903113)
        ·
          refine ⟨18208767883422674106677335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24278357177896898808903113 18208767883422674106677335)
          ·
            refine ⟨27313151825134011160016003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18208767883422674106677335 27313151825134011160016003)
            ·
              refine ⟨40969727737701016740024005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27313151825134011160016003 40969727737701016740024005)
              ·
                refine ⟨7681823950818940638754501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40969727737701016740024005 7681823950818940638754501)
                ·
                  refine ⟨1440341990778551369766469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7681823950818940638754501 1440341990778551369766469)
                  ·
                    refine ⟨270064123270978381831213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1440341990778551369766469 270064123270978381831213)
                    ·
                      rfl

theorem cell22_788922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 4, 4].length) (baseStart_788922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_788922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_788922 prefixEnd_788922 := by exact prefixLift 788922
  have htrace : WordTrace (prefixWord ++ tailWord_788922) baseStart_788922 baseEnd_788922 := by
    simpa [prefixWord, tailWord_788922, baseEnd_788922] using wordTrace_append hprefix tailTrace_788922
  have hstable : (prefixWord ++ tailWord_788922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788922).length < 2 ^ (prefixWord ++ tailWord_788922).sum := by decide
  have hdescent : baseEnd_788922 < baseStart_788922 := by decide
  rcases family_descends (prefixWord ++ tailWord_788922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788924 : List Nat := [2, 2, 2, 4, 1, 1, 1, 3, 1, 5]
def baseStart_788924 : Nat := 118140960795 + 788924 * 2 ^ 59
def prefixEnd_788924 : Nat := 4983230072969 + 3 ^ 40 * 788924 * 2
def baseEnd_788924 : Nat := 270064807911851043281207

theorem tailTrace_788924 : CollatzResearch.WordTrace tailWord_788924 prefixEnd_788924 270064807911851043281207 := by
  unfold tailWord_788924
  simp only [CollatzResearch.WordTrace]
  refine ⟨14387211096935280168654913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19182948129247040224873217 14387211096935280168654913)
  ·
    refine ⟨10790408322701460126491185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14387211096935280168654913 10790408322701460126491185)
    ·
      refine ⟨8092806242026095094868389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10790408322701460126491185 8092806242026095094868389)
      ·
        refine ⟨1517401170379892830287823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8092806242026095094868389 1517401170379892830287823)
        ·
          refine ⟨2276101755569839245431735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1517401170379892830287823 2276101755569839245431735)
          ·
            refine ⟨3414152633354758868147603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2276101755569839245431735 3414152633354758868147603)
            ·
              refine ⟨5121228950032138302221405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3414152633354758868147603 5121228950032138302221405)
              ·
                refine ⟨1920460856262051863333027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5121228950032138302221405 1920460856262051863333027)
                ·
                  refine ⟨2880691284393077794999541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1920460856262051863333027 2880691284393077794999541)
                  ·
                    refine ⟨270064807911851043281207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2880691284393077794999541 270064807911851043281207)
                    ·
                      rfl

theorem cell22_788924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_788924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_788924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_788924 prefixEnd_788924 := by exact prefixLift 788924
  have htrace : WordTrace (prefixWord ++ tailWord_788924) baseStart_788924 baseEnd_788924 := by
    simpa [prefixWord, tailWord_788924, baseEnd_788924] using wordTrace_append hprefix tailTrace_788924
  have hstable : (prefixWord ++ tailWord_788924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788924).length < 2 ^ (prefixWord ++ tailWord_788924).sum := by decide
  have hdescent : baseEnd_788924 < baseStart_788924 := by decide
  rcases family_descends (prefixWord ++ tailWord_788924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788997 : List Nat := [1, 3, 1, 1, 2, 2, 2, 2, 1, 7]
def baseStart_788997 : Nat := 118140960795 + 788997 * 2 ^ 59
def prefixEnd_788997 : Nat := 4983230072969 + 3 ^ 40 * 788997 * 2
def baseEnd_788997 : Nat := 270089797303703186205983

theorem tailTrace_788997 : CollatzResearch.WordTrace tailWord_788997 prefixEnd_788997 270089797303703186205983 := by
  unfold tailWord_788997
  simp only [CollatzResearch.WordTrace]
  refine ⟨28777084722606093804717245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19184723148404062536478163 28777084722606093804717245)
  ·
    refine ⟨10791406770977285176768967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28777084722606093804717245 10791406770977285176768967)
    ·
      refine ⟨16187110156465927765153451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10791406770977285176768967 16187110156465927765153451)
      ·
        refine ⟨24280665234698891647730177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16187110156465927765153451 24280665234698891647730177)
        ·
          refine ⟨18210498926024168735797633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24280665234698891647730177 18210498926024168735797633)
          ·
            refine ⟨13657874194518126551848225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18210498926024168735797633 13657874194518126551848225)
            ·
              refine ⟨10243405645888594913886169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13657874194518126551848225 10243405645888594913886169)
              ·
                refine ⟨7682554234416446185414627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10243405645888594913886169 7682554234416446185414627)
                ·
                  refine ⟨11523831351624669278121941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7682554234416446185414627 11523831351624669278121941)
                  ·
                    refine ⟨270089797303703186205983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11523831351624669278121941 270089797303703186205983)
                    ·
                      rfl

theorem cell22_788997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 7].length) (baseStart_788997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_788997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_788997 prefixEnd_788997 := by exact prefixLift 788997
  have htrace : WordTrace (prefixWord ++ tailWord_788997) baseStart_788997 baseEnd_788997 := by
    simpa [prefixWord, tailWord_788997, baseEnd_788997] using wordTrace_append hprefix tailTrace_788997
  have hstable : (prefixWord ++ tailWord_788997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788997).length < 2 ^ (prefixWord ++ tailWord_788997).sum := by decide
  have hdescent : baseEnd_788997 < baseStart_788997 := by decide
  rcases family_descends (prefixWord ++ tailWord_788997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789003 : List Nat := [1, 1, 1, 1, 7, 1, 3, 3, 1, 3]
def baseStart_789003 : Nat := 118140960795 + 789003 * 2 ^ 59
def prefixEnd_789003 : Nat := 4983230072969 + 3 ^ 40 * 789003 * 2
def baseEnd_789003 : Nat := 270091851226321170555965

theorem tailTrace_789003 : CollatzResearch.WordTrace tailWord_789003 prefixEnd_789003 270091851226321170555965 := by
  unfold tailWord_789003
  simp only [CollatzResearch.WordTrace]
  refine ⟨28777303560584356829435663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19184869040389571219623775 28777303560584356829435663)
  ·
    refine ⟨43165955340876535244153495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28777303560584356829435663 43165955340876535244153495)
    ·
      refine ⟨64748933011314802866230243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43165955340876535244153495 64748933011314802866230243)
      ·
        refine ⟨97123399516972204299345365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64748933011314802866230243 97123399516972204299345365)
        ·
          refine ⟨2276329676179036038265907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 97123399516972204299345365 2276329676179036038265907)
          ·
            refine ⟨3414494514268554057398861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2276329676179036038265907 3414494514268554057398861)
            ·
              refine ⟨1280435442850707771524573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3414494514268554057398861 1280435442850707771524573)
              ·
                refine ⟨480163291069015414321715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1280435442850707771524573 480163291069015414321715)
                ·
                  refine ⟨720244936603523121482573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 480163291069015414321715 720244936603523121482573)
                  ·
                    refine ⟨270091851226321170555965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 720244936603523121482573 270091851226321170555965)
                    ·
                      rfl

theorem cell22_789003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 3, 1, 3].length) (baseStart_789003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_789003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_789003 prefixEnd_789003 := by exact prefixLift 789003
  have htrace : WordTrace (prefixWord ++ tailWord_789003) baseStart_789003 baseEnd_789003 := by
    simpa [prefixWord, tailWord_789003, baseEnd_789003] using wordTrace_append hprefix tailTrace_789003
  have hstable : (prefixWord ++ tailWord_789003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789003).length < 2 ^ (prefixWord ++ tailWord_789003).sum := by decide
  have hdescent : baseEnd_789003 < baseStart_789003 := by decide
  rcases family_descends (prefixWord ++ tailWord_789003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789020 : List Nat := [2, 2, 3, 1, 2, 3, 3, 2, 1, 3]
def baseStart_789020 : Nat := 118140960795 + 789020 * 2 ^ 59
def prefixEnd_789020 : Nat := 4983230072969 + 3 ^ 40 * 789020 * 2
def baseEnd_789020 : Nat := 270097670673738792880913

theorem tailTrace_789020 : CollatzResearch.WordTrace tailWord_789020 prefixEnd_789020 270097670673738792880913 := by
  unfold tailWord_789020
  simp only [CollatzResearch.WordTrace]
  refine ⟨14388961800761384366402257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19185282401015179155203009 14388961800761384366402257)
  ·
    refine ⟨10791721350571038274801693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14388961800761384366402257 10791721350571038274801693)
    ·
      refine ⟨4046895506464139353050635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10791721350571038274801693 4046895506464139353050635)
      ·
        refine ⟨6070343259696209029575953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4046895506464139353050635 6070343259696209029575953)
        ·
          refine ⟨4552757444772156772181965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6070343259696209029575953 4552757444772156772181965)
          ·
            refine ⟨1707284041789558789568237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4552757444772156772181965 1707284041789558789568237)
            ·
              refine ⟨640231515671084546088089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1707284041789558789568237 640231515671084546088089)
              ·
                refine ⟨480173636753313409566067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 640231515671084546088089 480173636753313409566067)
                ·
                  refine ⟨720260455129970114349101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 480173636753313409566067 720260455129970114349101)
                  ·
                    refine ⟨270097670673738792880913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 720260455129970114349101 270097670673738792880913)
                    ·
                      rfl

theorem cell22_789020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_789020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_789020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_789020 prefixEnd_789020 := by exact prefixLift 789020
  have htrace : WordTrace (prefixWord ++ tailWord_789020) baseStart_789020 baseEnd_789020 := by
    simpa [prefixWord, tailWord_789020, baseEnd_789020] using wordTrace_append hprefix tailTrace_789020
  have hstable : (prefixWord ++ tailWord_789020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789020).length < 2 ^ (prefixWord ++ tailWord_789020).sum := by decide
  have hdescent : baseEnd_789020 < baseStart_789020 := by decide
  rcases family_descends (prefixWord ++ tailWord_789020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789059 : List Nat := [1, 1, 1, 3, 1, 2, 1, 3, 6, 3]
def baseStart_789059 : Nat := 118140960795 + 789059 * 2 ^ 59
def prefixEnd_789059 : Nat := 4983230072969 + 3 ^ 40 * 789059 * 2
def baseEnd_789059 : Nat := 270111021170755691155793

theorem tailTrace_789059 : CollatzResearch.WordTrace tailWord_789059 prefixEnd_789059 270111021170755691155793 := by
  unfold tailWord_789059
  simp only [CollatzResearch.WordTrace]
  refine ⟨28779346048381478393474231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19186230698920985595649487 28779346048381478393474231)
  ·
    refine ⟨43169019072572217590211347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28779346048381478393474231 43169019072572217590211347)
    ·
      refine ⟨64753528608858326385317021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43169019072572217590211347 64753528608858326385317021)
      ·
        refine ⟨24282573228321872394493883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64753528608858326385317021 24282573228321872394493883)
        ·
          refine ⟨36423859842482808591740825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24282573228321872394493883 36423859842482808591740825)
          ·
            refine ⟨27317894881862106443805619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36423859842482808591740825 27317894881862106443805619)
            ·
              refine ⟨40976842322793159665708429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27317894881862106443805619 40976842322793159665708429)
              ·
                refine ⟨15366315871047434874640661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40976842322793159665708429 15366315871047434874640661)
                ·
                  refine ⟨720296056455348509748781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 15366315871047434874640661 720296056455348509748781)
                  ·
                    refine ⟨270111021170755691155793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 720296056455348509748781 270111021170755691155793)
                    ·
                      rfl

theorem cell22_789059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 6, 3].length) (baseStart_789059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_789059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_789059 prefixEnd_789059 := by exact prefixLift 789059
  have htrace : WordTrace (prefixWord ++ tailWord_789059) baseStart_789059 baseEnd_789059 := by
    simpa [prefixWord, tailWord_789059, baseEnd_789059] using wordTrace_append hprefix tailTrace_789059
  have hstable : (prefixWord ++ tailWord_789059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789059).length < 2 ^ (prefixWord ++ tailWord_789059).sum := by decide
  have hdescent : baseEnd_789059 < baseStart_789059 := by decide
  rcases family_descends (prefixWord ++ tailWord_789059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789063 : List Nat := [1, 1, 4, 1, 4, 2, 3, 1, 1, 4]
def baseStart_789063 : Nat := 118140960795 + 789063 * 2 ^ 59
def prefixEnd_789063 : Nat := 4983230072969 + 3 ^ 40 * 789063 * 2
def baseEnd_789063 : Nat := 270112390452501014055781

theorem tailTrace_789063 : CollatzResearch.WordTrace tailWord_789063 prefixEnd_789063 270112390452501014055781 := by
  unfold tailWord_789063
  simp only [CollatzResearch.WordTrace]
  refine ⟨28779491940366987076619843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19186327960244658051079895 28779491940366987076619843)
  ·
    refine ⟨43169237910550480614929765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28779491940366987076619843 43169237910550480614929765)
    ·
      refine ⟨8094232108228215115299331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43169237910550480614929765 8094232108228215115299331)
      ·
        refine ⟨12141348162342322672948997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8094232108228215115299331 12141348162342322672948997)
        ·
          refine ⟨2276502780439185501177937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12141348162342322672948997 2276502780439185501177937)
          ·
            refine ⟨1707377085329389125883453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2276502780439185501177937 1707377085329389125883453)
            ·
              refine ⟨640266406998520922206295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1707377085329389125883453 640266406998520922206295)
              ·
                refine ⟨960399610497781383309443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 640266406998520922206295 960399610497781383309443)
                ·
                  refine ⟨1440599415746672074964165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 960399610497781383309443 1440599415746672074964165)
                  ·
                    refine ⟨270112390452501014055781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1440599415746672074964165 270112390452501014055781)
                    ·
                      rfl

theorem cell22_789063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 1, 1, 4].length) (baseStart_789063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_789063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_789063 prefixEnd_789063 := by exact prefixLift 789063
  have htrace : WordTrace (prefixWord ++ tailWord_789063) baseStart_789063 baseEnd_789063 := by
    simpa [prefixWord, tailWord_789063, baseEnd_789063] using wordTrace_append hprefix tailTrace_789063
  have hstable : (prefixWord ++ tailWord_789063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789063).length < 2 ^ (prefixWord ++ tailWord_789063).sum := by decide
  have hdescent : baseEnd_789063 < baseStart_789063 := by decide
  rcases family_descends (prefixWord ++ tailWord_789063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789089 : List Nat := [1, 2, 3, 1, 1, 4, 3, 7]
def baseStart_789089 : Nat := 118140960795 + 789089 * 2 ^ 59
def prefixEnd_789089 : Nat := 4983230072969 + 3 ^ 40 * 789089 * 2
def baseEnd_789089 : Nat := 30013476753760623656189

theorem tailTrace_789089 : CollatzResearch.WordTrace tailWord_789089 prefixEnd_789089 30013476753760623656189 := by
  unfold tailWord_789089
  simp only [CollatzResearch.WordTrace]
  refine ⟨28780440238272793517066321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19186960158848529011377547 28780440238272793517066321)
  ·
    refine ⟨21585330178704595137799741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28780440238272793517066321 21585330178704595137799741)
    ·
      refine ⟨8094498817014223176674903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21585330178704595137799741 8094498817014223176674903)
      ·
        refine ⟨12141748225521334765012355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8094498817014223176674903 12141748225521334765012355)
        ·
          refine ⟨18212622338282002147518533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12141748225521334765012355 18212622338282002147518533)
          ·
            refine ⟨3414866688427875402659725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18212622338282002147518533 3414866688427875402659725)
            ·
              refine ⟨1280575008160453275997397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3414866688427875402659725 1280575008160453275997397)
              ·
                refine ⟨30013476753760623656189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1280575008160453275997397 30013476753760623656189)
                ·
                  rfl

theorem cell22_789089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 7].length) (baseStart_789089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_789089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_789089 prefixEnd_789089 := by exact prefixLift 789089
  have htrace : WordTrace (prefixWord ++ tailWord_789089) baseStart_789089 baseEnd_789089 := by
    simpa [prefixWord, tailWord_789089, baseEnd_789089] using wordTrace_append hprefix tailTrace_789089
  have hstable : (prefixWord ++ tailWord_789089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789089).length < 2 ^ (prefixWord ++ tailWord_789089).sum := by decide
  have hdescent : baseEnd_789089 < baseStart_789089 := by decide
  rcases family_descends (prefixWord ++ tailWord_789089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789121 : List Nat := [1, 2, 4, 2, 1, 1, 1, 2, 5, 3]
def baseStart_789121 : Nat := 118140960795 + 789121 * 2 ^ 59
def prefixEnd_789121 : Nat := 4983230072969 + 3 ^ 40 * 789121 * 2
def baseEnd_789121 : Nat := 270132245037808196105603

theorem tailTrace_789121 : CollatzResearch.WordTrace tailWord_789121 prefixEnd_789121 270132245037808196105603 := by
  unfold tailWord_789121
  simp only [CollatzResearch.WordTrace]
  refine ⟨28781607374156862982231217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19187738249437908654820811 28781607374156862982231217)
  ·
    refine ⟨21586205530617647236673413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28781607374156862982231217 21586205530617647236673413)
    ·
      refine ⟨4047413536990808856876265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21586205530617647236673413 4047413536990808856876265)
      ·
        refine ⟨3035560152743106642657199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4047413536990808856876265 3035560152743106642657199)
        ·
          refine ⟨4553340229114659963985799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3035560152743106642657199 4553340229114659963985799)
          ·
            refine ⟨6830010343671989945978699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4553340229114659963985799 6830010343671989945978699)
            ·
              refine ⟨10245015515507984918968049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6830010343671989945978699 10245015515507984918968049)
              ·
                refine ⟨7683761636630988689226037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10245015515507984918968049 7683761636630988689226037)
                ·
                  refine ⟨720352653434155189614941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7683761636630988689226037 720352653434155189614941)
                  ·
                    refine ⟨270132245037808196105603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 720352653434155189614941 270132245037808196105603)
                    ·
                      rfl

theorem cell22_789121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_789121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_789121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_789121 prefixEnd_789121 := by exact prefixLift 789121
  have htrace : WordTrace (prefixWord ++ tailWord_789121) baseStart_789121 baseEnd_789121 := by
    simpa [prefixWord, tailWord_789121, baseEnd_789121] using wordTrace_append hprefix tailTrace_789121
  have hstable : (prefixWord ++ tailWord_789121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789121).length < 2 ^ (prefixWord ++ tailWord_789121).sum := by decide
  have hdescent : baseEnd_789121 < baseStart_789121 := by decide
  rcases family_descends (prefixWord ++ tailWord_789121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789138 : List Nat := [3, 2, 3, 1, 2, 1, 1, 3, 3, 3]
def baseStart_789138 : Nat := 118140960795 + 789138 * 2 ^ 59
def prefixEnd_789138 : Nat := 4983230072969 + 3 ^ 40 * 789138 * 2
def baseEnd_789138 : Nat := 270138064485225818430551

theorem tailTrace_789138 : CollatzResearch.WordTrace tailWord_789138 prefixEnd_789138 270138064485225818430551 := by
  unfold tailWord_789138
  simp only [CollatzResearch.WordTrace]
  refine ⟨7195556853773818721400017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19188151610063516590400045 7195556853773818721400017)
  ·
    refine ⟨5396667640330364041050013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7195556853773818721400017 5396667640330364041050013)
    ·
      refine ⟨2023750365123886515393755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5396667640330364041050013 2023750365123886515393755)
      ·
        refine ⟨3035625547685829773090633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2023750365123886515393755 3035625547685829773090633)
        ·
          refine ⟨2276719160764372329817975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3035625547685829773090633 2276719160764372329817975)
          ·
            refine ⟨3415078741146558494726963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2276719160764372329817975 3415078741146558494726963)
            ·
              refine ⟨5122618111719837742090445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3415078741146558494726963 5122618111719837742090445)
              ·
                refine ⟨1920981791894939153283917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5122618111719837742090445 1920981791894939153283917)
                ·
                  refine ⟨720368171960602182481469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1920981791894939153283917 720368171960602182481469)
                  ·
                    refine ⟨270138064485225818430551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 720368171960602182481469 270138064485225818430551)
                    ·
                      rfl

theorem cell22_789138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_789138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_789138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_789138 prefixEnd_789138 := by exact prefixLift 789138
  have htrace : WordTrace (prefixWord ++ tailWord_789138) baseStart_789138 baseEnd_789138 := by
    simpa [prefixWord, tailWord_789138, baseEnd_789138] using wordTrace_append hprefix tailTrace_789138
  have hstable : (prefixWord ++ tailWord_789138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789138).length < 2 ^ (prefixWord ++ tailWord_789138).sum := by decide
  have hdescent : baseEnd_789138 < baseStart_789138 := by decide
  rcases family_descends (prefixWord ++ tailWord_789138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789202 : List Nat := [3, 2, 2, 2, 4, 1, 2, 1, 5]
def baseStart_789202 : Nat := 118140960795 + 789202 * 2 ^ 59
def prefixEnd_789202 : Nat := 4983230072969 + 3 ^ 40 * 789202 * 2
def baseEnd_789202 : Nat := 90053324331050328276785

theorem tailTrace_789202 : CollatzResearch.WordTrace tailWord_789202 prefixEnd_789202 90053324331050328276785 := by
  unfold tailWord_789202
  simp only [CollatzResearch.WordTrace]
  refine ⟨7196140421715853453982465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19189707791242275877286573 7196140421715853453982465)
  ·
    refine ⟨5397105316286890090486849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7196140421715853453982465 5397105316286890090486849)
    ·
      refine ⟨4047828987215167567865137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5397105316286890090486849 4047828987215167567865137)
      ·
        refine ⟨3035871740411375675898853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4047828987215167567865137 3035871740411375675898853)
        ·
          refine ⟨569225951327132939231035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3035871740411375675898853 569225951327132939231035)
          ·
            refine ⟨853838926990699408846553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 569225951327132939231035 853838926990699408846553)
            ·
              refine ⟨640379195243024556634915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 853838926990699408846553 640379195243024556634915)
              ·
                refine ⟨960568792864536834952373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 640379195243024556634915 960568792864536834952373)
                ·
                  refine ⟨90053324331050328276785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 960568792864536834952373 90053324331050328276785)
                  ·
                    rfl

theorem cell22_789202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 1, 5].length) (baseStart_789202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_789202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_789202 prefixEnd_789202 := by exact prefixLift 789202
  have htrace : WordTrace (prefixWord ++ tailWord_789202) baseStart_789202 baseEnd_789202 := by
    simpa [prefixWord, tailWord_789202, baseEnd_789202] using wordTrace_append hprefix tailTrace_789202
  have hstable : (prefixWord ++ tailWord_789202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789202).length < 2 ^ (prefixWord ++ tailWord_789202).sum := by decide
  have hdescent : baseEnd_789202 < baseStart_789202 := by decide
  rcases family_descends (prefixWord ++ tailWord_789202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789277 : List Nat := [1, 4, 2, 4, 1, 2, 1, 1, 2, 4]
def baseStart_789277 : Nat := 118140960795 + 789277 * 2 ^ 59
def prefixEnd_789277 : Nat := 4983230072969 + 3 ^ 40 * 789277 * 2
def baseEnd_789277 : Nat := 270185647025875789205125

theorem tailTrace_789277 : CollatzResearch.WordTrace tailWord_789277 prefixEnd_789277 270185647025875789205125 := by
  unfold tailWord_789277
  simp only [CollatzResearch.WordTrace]
  refine ⟨28787297161591701624910085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19191531441061134416606723 28787297161591701624910085)
  ·
    refine ⟨5397618217798444054670641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28787297161591701624910085 5397618217798444054670641)
    ·
      refine ⟨4048213663348833041002981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5397618217798444054670641 4048213663348833041002981)
      ·
        refine ⟨759040061877906195188059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4048213663348833041002981 759040061877906195188059)
        ·
          refine ⟨1138560092816859292782089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 759040061877906195188059 1138560092816859292782089)
          ·
            refine ⟨853920069612644469586567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1138560092816859292782089 853920069612644469586567)
            ·
              refine ⟨1280880104418966704379851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 853920069612644469586567 1280880104418966704379851)
              ·
                refine ⟨1921320156628450056569777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1280880104418966704379851 1921320156628450056569777)
                ·
                  refine ⟨1440990117471337542427333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1921320156628450056569777 1440990117471337542427333)
                  ·
                    refine ⟨270185647025875789205125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1440990117471337542427333 270185647025875789205125)
                    ·
                      rfl

theorem cell22_789277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_789277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_789277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_789277 prefixEnd_789277 := by exact prefixLift 789277
  have htrace : WordTrace (prefixWord ++ tailWord_789277) baseStart_789277 baseEnd_789277 := by
    simpa [prefixWord, tailWord_789277, baseEnd_789277] using wordTrace_append hprefix tailTrace_789277
  have hstable : (prefixWord ++ tailWord_789277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789277).length < 2 ^ (prefixWord ++ tailWord_789277).sum := by decide
  have hdescent : baseEnd_789277 < baseStart_789277 := by decide
  rcases family_descends (prefixWord ++ tailWord_789277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789363 : List Nat := [1, 1, 1, 2, 2, 1, 6, 1, 4, 3]
def baseStart_789363 : Nat := 118140960795 + 789363 * 2 ^ 59
def prefixEnd_789363 : Nat := 4983230072969 + 3 ^ 40 * 789363 * 2
def baseEnd_789363 : Nat := 270215086583400231554861

theorem tailTrace_789363 : CollatzResearch.WordTrace tailWord_789363 prefixEnd_789363 270215086583400231554861 := by
  unfold tailWord_789363
  simp only [CollatzResearch.WordTrace]
  refine ⟨28790433839280138312540743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19193622559520092208360495 28790433839280138312540743)
  ·
    refine ⟨43185650758920207468811115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28790433839280138312540743 43185650758920207468811115)
    ·
      refine ⟨64778476138380311203216673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43185650758920207468811115 64778476138380311203216673)
      ·
        refine ⟨48583857103785233402412505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64778476138380311203216673 48583857103785233402412505)
        ·
          refine ⟨36437892827838925051809379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48583857103785233402412505 36437892827838925051809379)
          ·
            refine ⟨54656839241758387577714069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36437892827838925051809379 54656839241758387577714069)
            ·
              refine ⟨2562039339457424417705347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 54656839241758387577714069 2562039339457424417705347)
              ·
                refine ⟨3843059009186136626558021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2562039339457424417705347 3843059009186136626558021)
                ·
                  refine ⟨720573564222400617479629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3843059009186136626558021 720573564222400617479629)
                  ·
                    refine ⟨270215086583400231554861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 720573564222400617479629 270215086583400231554861)
                    ·
                      rfl

theorem cell22_789363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 4, 3].length) (baseStart_789363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_789363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_789363 prefixEnd_789363 := by exact prefixLift 789363
  have htrace : WordTrace (prefixWord ++ tailWord_789363) baseStart_789363 baseEnd_789363 := by
    simpa [prefixWord, tailWord_789363, baseEnd_789363] using wordTrace_append hprefix tailTrace_789363
  have hstable : (prefixWord ++ tailWord_789363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789363).length < 2 ^ (prefixWord ++ tailWord_789363).sum := by decide
  have hdescent : baseEnd_789363 < baseStart_789363 := by decide
  rcases family_descends (prefixWord ++ tailWord_789363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789365 : List Nat := [1, 3, 4, 1, 1, 4, 1, 1, 6]
def baseStart_789365 : Nat := 118140960795 + 789365 * 2 ^ 59
def prefixEnd_789365 : Nat := 4983230072969 + 3 ^ 40 * 789365 * 2
def baseEnd_789365 : Nat := 90071923741424297668285

theorem tailTrace_789365 : CollatzResearch.WordTrace tailWord_789365 prefixEnd_789365 90071923741424297668285 := by
  unfold tailWord_789365
  simp only [CollatzResearch.WordTrace]
  refine ⟨28790506785272892654113549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19193671190181928436075699 28790506785272892654113549)
  ·
    refine ⟨10796440044477334745292581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28790506785272892654113549 10796440044477334745292581)
    ·
      refine ⟨2024332508339500264742359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10796440044477334745292581 2024332508339500264742359)
      ·
        refine ⟨3036498762509250397113539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2024332508339500264742359 3036498762509250397113539)
        ·
          refine ⟨4554748143763875595670309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3036498762509250397113539 4554748143763875595670309)
          ·
            refine ⟨854015276955726674188183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4554748143763875595670309 854015276955726674188183)
            ·
              refine ⟨1281022915433590011282275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 854015276955726674188183 1281022915433590011282275)
              ·
                refine ⟨1921534373150385016923413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1281022915433590011282275 1921534373150385016923413)
                ·
                  refine ⟨90071923741424297668285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1921534373150385016923413 90071923741424297668285)
                  ·
                    rfl

theorem cell22_789365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 6].length) (baseStart_789365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_789365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_789365 prefixEnd_789365 := by exact prefixLift 789365
  have htrace : WordTrace (prefixWord ++ tailWord_789365) baseStart_789365 baseEnd_789365 := by
    simpa [prefixWord, tailWord_789365, baseEnd_789365] using wordTrace_append hprefix tailTrace_789365
  have hstable : (prefixWord ++ tailWord_789365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789365).length < 2 ^ (prefixWord ++ tailWord_789365).sum := by decide
  have hdescent : baseEnd_789365 < baseStart_789365 := by decide
  rcases family_descends (prefixWord ++ tailWord_789365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789446 : List Nat := [6, 1, 3, 1, 1, 1, 1, 1, 1, 6]
def baseStart_789446 : Nat := 118140960795 + 789446 * 2 ^ 59
def prefixEnd_789446 : Nat := 4983230072969 + 3 ^ 40 * 789446 * 2
def baseEnd_789446 : Nat := 270243499179615681729607

theorem tailTrace_789446 : CollatzResearch.WordTrace tailWord_789446 prefixEnd_789446 270243499179615681729607 := by
  unfold tailWord_789446
  simp only [CollatzResearch.WordTrace]
  refine ⟨899795659311857608994131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19195640731986295658541461 899795659311857608994131)
  ·
    refine ⟨1349693488967786413491197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 899795659311857608994131 1349693488967786413491197)
    ·
      refine ⟨506135058362919905059199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1349693488967786413491197 506135058362919905059199)
      ·
        refine ⟨759202587544379857588799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 506135058362919905059199 759202587544379857588799)
        ·
          refine ⟨1138803881316569786383199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 759202587544379857588799 1138803881316569786383199)
          ·
            refine ⟨1708205821974854679574799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1138803881316569786383199 1708205821974854679574799)
            ·
              refine ⟨2562308732962282019362199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1708205821974854679574799 2562308732962282019362199)
              ·
                refine ⟨3843463099443423029043299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2562308732962282019362199 3843463099443423029043299)
                ·
                  refine ⟨5765194649165134543564949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3843463099443423029043299 5765194649165134543564949)
                  ·
                    refine ⟨270243499179615681729607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5765194649165134543564949 270243499179615681729607)
                    ·
                      rfl

theorem cell22_789446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_789446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_789446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_789446 prefixEnd_789446 := by exact prefixLift 789446
  have htrace : WordTrace (prefixWord ++ tailWord_789446) baseStart_789446 baseEnd_789446 := by
    simpa [prefixWord, tailWord_789446, baseEnd_789446] using wordTrace_append hprefix tailTrace_789446
  have hstable : (prefixWord ++ tailWord_789446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789446).length < 2 ^ (prefixWord ++ tailWord_789446).sum := by decide
  have hdescent : baseEnd_789446 < baseStart_789446 := by decide
  rcases family_descends (prefixWord ++ tailWord_789446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789513 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 6, 4]
def baseStart_789513 : Nat := 118140960795 + 789513 * 2 ^ 59
def prefixEnd_789513 : Nat := 4983230072969 + 3 ^ 40 * 789513 * 2
def baseEnd_789513 : Nat := 270266434648849840304401

theorem tailTrace_789513 : CollatzResearch.WordTrace tailWord_789513 prefixEnd_789513 270266434648849840304401 := by
  unfold tailWord_789513
  simp only [CollatzResearch.WordTrace]
  refine ⟨28795904788736713930501193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19197269859157809287000795 28795904788736713930501193)
  ·
    refine ⟨21596928591552535447875895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28795904788736713930501193 21596928591552535447875895)
    ·
      refine ⟨32395392887328803171813843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21596928591552535447875895 32395392887328803171813843)
      ·
        refine ⟨48593089330993204757720765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32395392887328803171813843 48593089330993204757720765)
        ·
          refine ⟨18222408499122451784145287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48593089330993204757720765 18222408499122451784145287)
          ·
            refine ⟨27333612748683677676217931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18222408499122451784145287 27333612748683677676217931)
            ·
              refine ⟨41000419123025516514326897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27333612748683677676217931 41000419123025516514326897)
              ·
                refine ⟨30750314342269137385745173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41000419123025516514326897 30750314342269137385745173)
                ·
                  refine ⟨1441420984793865814956805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 30750314342269137385745173 1441420984793865814956805)
                  ·
                    refine ⟨270266434648849840304401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1441420984793865814956805 270266434648849840304401)
                    ·
                      rfl

theorem cell22_789513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 6, 4].length) (baseStart_789513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_789513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_789513 prefixEnd_789513 := by exact prefixLift 789513
  have htrace : WordTrace (prefixWord ++ tailWord_789513) baseStart_789513 baseEnd_789513 := by
    simpa [prefixWord, tailWord_789513, baseEnd_789513] using wordTrace_append hprefix tailTrace_789513
  have hstable : (prefixWord ++ tailWord_789513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789513).length < 2 ^ (prefixWord ++ tailWord_789513).sum := by decide
  have hdescent : baseEnd_789513 < baseStart_789513 := by decide
  rcases family_descends (prefixWord ++ tailWord_789513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789515 : List Nat := [1, 1, 1, 1, 6, 2, 1, 2, 4, 3]
def baseStart_789515 : Nat := 118140960795 + 789515 * 2 ^ 59
def prefixEnd_789515 : Nat := 4983230072969 + 3 ^ 40 * 789515 * 2
def baseEnd_789515 : Nat := 270267119289722501754395

theorem tailTrace_789515 : CollatzResearch.WordTrace tailWord_789515 prefixEnd_789515 270267119289722501754395 := by
  unfold tailWord_789515
  simp only [CollatzResearch.WordTrace]
  refine ⟨28795977734729468272073999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19197318489819645514715999 28795977734729468272073999)
  ·
    refine ⟨43193966602094202408110999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28795977734729468272073999 43193966602094202408110999)
    ·
      refine ⟨64790949903141303612166499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43193966602094202408110999 64790949903141303612166499)
      ·
        refine ⟨97186424854711955418249749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64790949903141303612166499 97186424854711955418249749)
        ·
          refine ⟨4555613665064622910230457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 97186424854711955418249749 4555613665064622910230457)
          ·
            refine ⟨3416710248798467182672843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4555613665064622910230457 3416710248798467182672843)
            ·
              refine ⟨5125065373197700774009265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3416710248798467182672843 5125065373197700774009265)
              ·
                refine ⟨3843799029898275580506949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5125065373197700774009265 3843799029898275580506949)
                ·
                  refine ⟨720712318105926671345053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3843799029898275580506949 720712318105926671345053)
                  ·
                    refine ⟨270267119289722501754395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 720712318105926671345053 270267119289722501754395)
                    ·
                      rfl

theorem cell22_789515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 4, 3].length) (baseStart_789515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_789515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_789515 prefixEnd_789515 := by exact prefixLift 789515
  have htrace : WordTrace (prefixWord ++ tailWord_789515) baseStart_789515 baseEnd_789515 := by
    simpa [prefixWord, tailWord_789515, baseEnd_789515] using wordTrace_append hprefix tailTrace_789515
  have hstable : (prefixWord ++ tailWord_789515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789515).length < 2 ^ (prefixWord ++ tailWord_789515).sum := by decide
  have hdescent : baseEnd_789515 < baseStart_789515 := by decide
  rcases family_descends (prefixWord ++ tailWord_789515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789528 : List Nat := [2, 1, 2, 3, 2, 2, 10]
def baseStart_789528 : Nat := 118140960795 + 789528 * 2 ^ 59
def prefixEnd_789528 : Nat := 4983230072969 + 3 ^ 40 * 789528 * 2
def baseEnd_789528 : Nat := 10010058127977585228865

theorem tailTrace_789528 : CollatzResearch.WordTrace tailWord_789528 prefixEnd_789528 10010058127977585228865 := by
  unfold tailWord_789528
  simp only [CollatzResearch.WordTrace]
  refine ⟨14398225941841185746148619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19197634589121580994864825 14398225941841185746148619)
  ·
    refine ⟨21597338912761778619222929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14398225941841185746148619 21597338912761778619222929)
    ·
      refine ⟨16198004184571333964417197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21597338912761778619222929 16198004184571333964417197)
      ·
        refine ⟨6074251569214250236656449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16198004184571333964417197 6074251569214250236656449)
        ·
          refine ⟨4555688676910687677492337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6074251569214250236656449 4555688676910687677492337)
          ·
            refine ⟨3416766507683015758119253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4555688676910687677492337 3416766507683015758119253)
            ·
              refine ⟨10010058127977585228865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3416766507683015758119253 10010058127977585228865)
              ·
                rfl

theorem cell22_789528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 10].length) (baseStart_789528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_789528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_789528 prefixEnd_789528 := by exact prefixLift 789528
  have htrace : WordTrace (prefixWord ++ tailWord_789528) baseStart_789528 baseEnd_789528 := by
    simpa [prefixWord, tailWord_789528, baseEnd_789528] using wordTrace_append hprefix tailTrace_789528
  have hstable : (prefixWord ++ tailWord_789528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789528).length < 2 ^ (prefixWord ++ tailWord_789528).sum := by decide
  have hdescent : baseEnd_789528 < baseStart_789528 := by decide
  rcases family_descends (prefixWord ++ tailWord_789528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789530 : List Nat := [3, 1, 1, 3, 1, 2, 3, 2, 2, 4]
def baseStart_789530 : Nat := 118140960795 + 789530 * 2 ^ 59
def prefixEnd_789530 : Nat := 4983230072969 + 3 ^ 40 * 789530 * 2
def baseEnd_789530 : Nat := 270272254096267462629349

theorem tailTrace_789530 : CollatzResearch.WordTrace tailWord_789530 prefixEnd_789530 270272254096267462629349 := by
  unfold tailWord_789530
  simp only [CollatzResearch.WordTrace]
  refine ⟨7199131207418781458467511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19197683219783417222580029 7199131207418781458467511)
  ·
    refine ⟨10798696811128172187701267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7199131207418781458467511 10798696811128172187701267)
    ·
      refine ⟨16198045216692258281551901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10798696811128172187701267 16198045216692258281551901)
      ·
        refine ⟨6074266956259596855581963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16198045216692258281551901 6074266956259596855581963)
        ·
          refine ⟨9111400434389395283372945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6074266956259596855581963 9111400434389395283372945)
          ·
            refine ⟨6833550325792046462529709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9111400434389395283372945 6833550325792046462529709)
            ·
              refine ⟨2562581372172017423448641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6833550325792046462529709 2562581372172017423448641)
              ·
                refine ⟨1921936029129013067586481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2562581372172017423448641 1921936029129013067586481)
                ·
                  refine ⟨1441452021846759800689861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1921936029129013067586481 1441452021846759800689861)
                  ·
                    refine ⟨270272254096267462629349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1441452021846759800689861 270272254096267462629349)
                    ·
                      rfl

theorem cell22_789530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 2, 4].length) (baseStart_789530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_789530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_789530 prefixEnd_789530 := by exact prefixLift 789530
  have htrace : WordTrace (prefixWord ++ tailWord_789530) baseStart_789530 baseEnd_789530 := by
    simpa [prefixWord, tailWord_789530, baseEnd_789530] using wordTrace_append hprefix tailTrace_789530
  have hstable : (prefixWord ++ tailWord_789530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789530).length < 2 ^ (prefixWord ++ tailWord_789530).sum := by decide
  have hdescent : baseEnd_789530 < baseStart_789530 := by decide
  rcases family_descends (prefixWord ++ tailWord_789530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789573 : List Nat := [1, 3, 1, 1, 1, 3, 2, 1, 9]
def baseStart_789573 : Nat := 118140960795 + 789573 * 2 ^ 59
def prefixEnd_789573 : Nat := 4983230072969 + 3 ^ 40 * 789573 * 2
def baseEnd_789573 : Nat := 90095657958343227934739

theorem tailTrace_789573 : CollatzResearch.WordTrace tailWord_789573 prefixEnd_789573 90095657958343227934739 := by
  unfold tailWord_789573
  simp only [CollatzResearch.WordTrace]
  refine ⟨28798093168519344177685373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19198728779012896118456915 28798093168519344177685373)
  ·
    refine ⟨10799284938194754066632015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28798093168519344177685373 10799284938194754066632015)
    ·
      refine ⟨16198927407292131099948023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10799284938194754066632015 16198927407292131099948023)
      ·
        refine ⟨24298391110938196649922035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16198927407292131099948023 24298391110938196649922035)
        ·
          refine ⟨36447586666407294974883053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24298391110938196649922035 36447586666407294974883053)
          ·
            refine ⟨13667844999902735615581145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36447586666407294974883053 13667844999902735615581145)
            ·
              refine ⟨10250883749927051711685859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13667844999902735615581145 10250883749927051711685859)
              ·
                refine ⟨15376325624890577567528789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10250883749927051711685859 15376325624890577567528789)
                ·
                  refine ⟨90095657958343227934739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 15376325624890577567528789 90095657958343227934739)
                  ·
                    rfl

theorem cell22_789573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 9].length) (baseStart_789573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_789573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_789573 prefixEnd_789573 := by exact prefixLift 789573
  have htrace : WordTrace (prefixWord ++ tailWord_789573) baseStart_789573 baseEnd_789573 := by
    simpa [prefixWord, tailWord_789573, baseEnd_789573] using wordTrace_append hprefix tailTrace_789573
  have hstable : (prefixWord ++ tailWord_789573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789573).length < 2 ^ (prefixWord ++ tailWord_789573).sum := by decide
  have hdescent : baseEnd_789573 < baseStart_789573 := by decide
  rcases family_descends (prefixWord ++ tailWord_789573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789605 : List Nat := [1, 3, 1, 3, 2, 1, 3, 1, 2, 5]
def baseStart_789605 : Nat := 118140960795 + 789605 * 2 ^ 59
def prefixEnd_789605 : Nat := 4983230072969 + 3 ^ 40 * 789605 * 2
def baseEnd_789605 : Nat := 270297928128992267004119

theorem tailTrace_789605 : CollatzResearch.WordTrace tailWord_789605 prefixEnd_789605 270297928128992267004119 := by
  unfold tailWord_789605
  simp only [CollatzResearch.WordTrace]
  refine ⟨28799260304403413642850269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19199506869602275761900179 28799260304403413642850269)
  ·
    refine ⟨10799722614151280116068851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28799260304403413642850269 10799722614151280116068851)
    ·
      refine ⟨16199583921226920174103277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10799722614151280116068851 16199583921226920174103277)
      ·
        refine ⟨6074843970460095065288729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16199583921226920174103277 6074843970460095065288729)
        ·
          refine ⟨4556132977845071298966547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6074843970460095065288729 4556132977845071298966547)
          ·
            refine ⟨6834199466767606948449821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4556132977845071298966547 6834199466767606948449821)
            ·
              refine ⟨2562824800037852605668683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6834199466767606948449821 2562824800037852605668683)
              ·
                refine ⟨3844237200056778908503025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2562824800037852605668683 3844237200056778908503025)
                ·
                  refine ⟨2883177900042584181377269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3844237200056778908503025 2883177900042584181377269)
                  ·
                    refine ⟨270297928128992267004119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2883177900042584181377269 270297928128992267004119)
                    ·
                      rfl

theorem cell22_789605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 5].length) (baseStart_789605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_789605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_789605 prefixEnd_789605 := by exact prefixLift 789605
  have htrace : WordTrace (prefixWord ++ tailWord_789605) baseStart_789605 baseEnd_789605 := by
    simpa [prefixWord, tailWord_789605, baseEnd_789605] using wordTrace_append hprefix tailTrace_789605
  have hstable : (prefixWord ++ tailWord_789605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789605).length < 2 ^ (prefixWord ++ tailWord_789605).sum := by decide
  have hdescent : baseEnd_789605 < baseStart_789605 := by decide
  rcases family_descends (prefixWord ++ tailWord_789605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789665 : List Nat := [1, 2, 3, 3, 1, 1, 1, 1, 3, 6]
def baseStart_789665 : Nat := 118140960795 + 789665 * 2 ^ 59
def prefixEnd_789665 : Nat := 4983230072969 + 3 ^ 40 * 789665 * 2
def baseEnd_789665 : Nat := 270318467355172110503935

theorem tailTrace_789665 : CollatzResearch.WordTrace tailWord_789665 prefixEnd_789665 270318467355172110503935 := by
  unfold tailWord_789665
  simp only [CollatzResearch.WordTrace]
  refine ⟨28801448684186043890034449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19200965789457362593356299 28801448684186043890034449)
  ·
    refine ⟨21601086513139532917525837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28801448684186043890034449 21601086513139532917525837)
    ·
      refine ⟨8100407442427324844072189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21601086513139532917525837 8100407442427324844072189)
      ·
        refine ⟨3037652790910246816527071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8100407442427324844072189 3037652790910246816527071)
        ·
          refine ⟨4556479186365370224790607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3037652790910246816527071 4556479186365370224790607)
          ·
            refine ⟨6834718779548055337185911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4556479186365370224790607 6834718779548055337185911)
            ·
              refine ⟨10252078169322083005778867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6834718779548055337185911 10252078169322083005778867)
              ·
                refine ⟨15378117253983124508668301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10252078169322083005778867 15378117253983124508668301)
                ·
                  refine ⟨5766793970243671690750613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15378117253983124508668301 5766793970243671690750613)
                  ·
                    refine ⟨270318467355172110503935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5766793970243671690750613 270318467355172110503935)
                    ·
                      rfl

theorem cell22_789665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_789665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_789665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_789665 prefixEnd_789665 := by exact prefixLift 789665
  have htrace : WordTrace (prefixWord ++ tailWord_789665) baseStart_789665 baseEnd_789665 := by
    simpa [prefixWord, tailWord_789665, baseEnd_789665] using wordTrace_append hprefix tailTrace_789665
  have hstable : (prefixWord ++ tailWord_789665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789665).length < 2 ^ (prefixWord ++ tailWord_789665).sum := by decide
  have hdescent : baseEnd_789665 < baseStart_789665 := by decide
  rcases family_descends (prefixWord ++ tailWord_789665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789667 : List Nat := [1, 1, 1, 4, 1, 1, 1, 7, 2, 3]
def baseStart_789667 : Nat := 118140960795 + 789667 * 2 ^ 59
def prefixEnd_789667 : Nat := 4983230072969 + 3 ^ 40 * 789667 * 2
def baseEnd_789667 : Nat := 270319151996044771953929

theorem tailTrace_789667 : CollatzResearch.WordTrace tailWord_789667 prefixEnd_789667 270319151996044771953929 := by
  unfold tailWord_789667
  simp only [CollatzResearch.WordTrace]
  refine ⟨28801521630178798231607255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19201014420119198821071503 28801521630178798231607255)
  ·
    refine ⟨43202282445268197347410883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28801521630178798231607255 43202282445268197347410883)
    ·
      refine ⟨64803423667902296021116325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43202282445268197347410883 64803423667902296021116325)
      ·
        refine ⟨12150641937731680503959311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64803423667902296021116325 12150641937731680503959311)
        ·
          refine ⟨18225962906597520755938967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12150641937731680503959311 18225962906597520755938967)
          ·
            refine ⟨27338944359896281133908451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18225962906597520755938967 27338944359896281133908451)
            ·
              refine ⟨41008416539844421700862677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27338944359896281133908451 41008416539844421700862677)
              ·
                refine ⟨961134762652603633613969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 41008416539844421700862677 961134762652603633613969)
                ·
                  refine ⟨720851071989452725210477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 961134762652603633613969 720851071989452725210477)
                  ·
                    refine ⟨270319151996044771953929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 720851071989452725210477 270319151996044771953929)
                    ·
                      rfl

theorem cell22_789667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 7, 2, 3].length) (baseStart_789667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_789667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_789667 prefixEnd_789667 := by exact prefixLift 789667
  have htrace : WordTrace (prefixWord ++ tailWord_789667) baseStart_789667 baseEnd_789667 := by
    simpa [prefixWord, tailWord_789667, baseEnd_789667] using wordTrace_append hprefix tailTrace_789667
  have hstable : (prefixWord ++ tailWord_789667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789667).length < 2 ^ (prefixWord ++ tailWord_789667).sum := by decide
  have hdescent : baseEnd_789667 < baseStart_789667 := by decide
  rcases family_descends (prefixWord ++ tailWord_789667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789697 : List Nat := [1, 2, 6, 1, 1, 1, 10]
def baseStart_789697 : Nat := 118140960795 + 789697 * 2 ^ 59
def prefixEnd_789697 : Nat := 4983230072969 + 3 ^ 40 * 789697 * 2
def baseEnd_789697 : Nat := 10012200800338321989031

theorem tailTrace_789697 : CollatzResearch.WordTrace tailWord_789697 prefixEnd_789697 10012200800338321989031 := by
  unfold tailWord_789697
  simp only [CollatzResearch.WordTrace]
  refine ⟨28802615820070113355199345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19201743880046742236799563 28802615820070113355199345)
  ·
    refine ⟨21601961865052585016399509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28802615820070113355199345 21601961865052585016399509)
    ·
      refine ⟨1012591962424339922643727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 21601961865052585016399509 1012591962424339922643727)
      ·
        refine ⟨1518887943636509883965591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1012591962424339922643727 1518887943636509883965591)
        ·
          refine ⟨2278331915454764825948387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1518887943636509883965591 2278331915454764825948387)
          ·
            refine ⟨3417497873182147238922581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2278331915454764825948387 3417497873182147238922581)
            ·
              refine ⟨10012200800338321989031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3417497873182147238922581 10012200800338321989031)
              ·
                rfl

theorem cell22_789697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 10].length) (baseStart_789697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_789697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_789697 prefixEnd_789697 := by exact prefixLift 789697
  have htrace : WordTrace (prefixWord ++ tailWord_789697) baseStart_789697 baseEnd_789697 := by
    simpa [prefixWord, tailWord_789697, baseEnd_789697] using wordTrace_append hprefix tailTrace_789697
  have hstable : (prefixWord ++ tailWord_789697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789697).length < 2 ^ (prefixWord ++ tailWord_789697).sum := by decide
  have hdescent : baseEnd_789697 < baseStart_789697 := by decide
  rcases family_descends (prefixWord ++ tailWord_789697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789718 : List Nat := [5, 2, 1, 2, 2, 1, 1, 3, 2, 3]
def baseStart_789718 : Nat := 118140960795 + 789718 * 2 ^ 59
def prefixEnd_789718 : Nat := 4983230072969 + 3 ^ 40 * 789718 * 2
def baseEnd_789718 : Nat := 270336610338297638928773

theorem tailTrace_789718 : CollatzResearch.WordTrace tailWord_789718 prefixEnd_789718 270336610338297638928773 := by
  unfold tailWord_789718
  simp only [CollatzResearch.WordTrace]
  refine ⟨1800211359562127121357113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19202254501996022627809205 1800211359562127121357113)
  ·
    refine ⟨1350158519671595341017835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1800211359562127121357113 1350158519671595341017835)
    ·
      refine ⟨2025237779507393011526753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1350158519671595341017835 2025237779507393011526753)
      ·
        refine ⟨1518928334630544758645065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2025237779507393011526753 1518928334630544758645065)
        ·
          refine ⟨1139196250972908568983799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1518928334630544758645065 1139196250972908568983799)
          ·
            refine ⟨1708794376459362853475699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1139196250972908568983799 1708794376459362853475699)
            ·
              refine ⟨2563191564689044280213549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1708794376459362853475699 2563191564689044280213549)
              ·
                refine ⟨961196836758391605080081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2563191564689044280213549 961196836758391605080081)
                ·
                  refine ⟨720897627568793703810061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 961196836758391605080081 720897627568793703810061)
                  ·
                    refine ⟨270336610338297638928773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 720897627568793703810061 270336610338297638928773)
                    ·
                      rfl

theorem cell22_789718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_789718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_789718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_789718 prefixEnd_789718 := by exact prefixLift 789718
  have htrace : WordTrace (prefixWord ++ tailWord_789718) baseStart_789718 baseEnd_789718 := by
    simpa [prefixWord, tailWord_789718, baseEnd_789718] using wordTrace_append hprefix tailTrace_789718
  have hstable : (prefixWord ++ tailWord_789718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789718).length < 2 ^ (prefixWord ++ tailWord_789718).sum := by decide
  have hdescent : baseEnd_789718 < baseStart_789718 := by decide
  rcases family_descends (prefixWord ++ tailWord_789718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789763 : List Nat := [1, 1, 1, 3, 2, 6, 2, 2, 1, 3]
def baseStart_789763 : Nat := 118140960795 + 789763 * 2 ^ 59
def prefixEnd_789763 : Nat := 4983230072969 + 3 ^ 40 * 789763 * 2
def baseEnd_789763 : Nat := 270352014757932521553635

theorem tailTrace_789763 : CollatzResearch.WordTrace tailWord_789763 prefixEnd_789763 270352014757932521553635 := by
  unfold tailWord_789763
  simp only [CollatzResearch.WordTrace]
  refine ⟨28805023037831006627101943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19203348691887337751401295 28805023037831006627101943)
  ·
    refine ⟨43207534556746509940652915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28805023037831006627101943 43207534556746509940652915)
    ·
      refine ⟨64811301835119764910979373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43207534556746509940652915 64811301835119764910979373)
      ·
        refine ⟨24304238188169911841617265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64811301835119764910979373 24304238188169911841617265)
        ·
          refine ⟨18228178641127433881212949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24304238188169911841617265 18228178641127433881212949)
          ·
            refine ⟨854445873802848463181857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 18228178641127433881212949 854445873802848463181857)
            ·
              refine ⟨640834405352136347386393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 854445873802848463181857 640834405352136347386393)
              ·
                refine ⟨480625804014102260539795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 640834405352136347386393 480625804014102260539795)
                ·
                  refine ⟨720938706021153390809693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 480625804014102260539795 720938706021153390809693)
                  ·
                    refine ⟨270352014757932521553635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 720938706021153390809693 270352014757932521553635)
                    ·
                      rfl

theorem cell22_789763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 2, 1, 3].length) (baseStart_789763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_789763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_789763 prefixEnd_789763 := by exact prefixLift 789763
  have htrace : WordTrace (prefixWord ++ tailWord_789763) baseStart_789763 baseEnd_789763 := by
    simpa [prefixWord, tailWord_789763, baseEnd_789763] using wordTrace_append hprefix tailTrace_789763
  have hstable : (prefixWord ++ tailWord_789763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789763).length < 2 ^ (prefixWord ++ tailWord_789763).sum := by decide
  have hdescent : baseEnd_789763 < baseStart_789763 := by decide
  rcases family_descends (prefixWord ++ tailWord_789763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789772 : List Nat := [2, 2, 1, 2, 2, 3, 1, 2, 3, 4]
def baseStart_789772 : Nat := 118140960795 + 789772 * 2 ^ 59
def prefixEnd_789772 : Nat := 4983230072969 + 3 ^ 40 * 789772 * 2
def baseEnd_789772 : Nat := 270355095641859498078607

theorem tailTrace_789772 : CollatzResearch.WordTrace tailWord_789772 prefixEnd_789772 270355095641859498078607 := by
  unfold tailWord_789772
  simp only [CollatzResearch.WordTrace]
  refine ⟨14402675647399200582089785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19203567529865600776119713 14402675647399200582089785)
  ·
    refine ⟨10802006735549400436567339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14402675647399200582089785 10802006735549400436567339)
    ·
      refine ⟨16203010103324100654851009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10802006735549400436567339 16203010103324100654851009)
      ·
        refine ⟨12152257577493075491138257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16203010103324100654851009 12152257577493075491138257)
        ·
          refine ⟨9114193183119806618353693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12152257577493075491138257 9114193183119806618353693)
          ·
            refine ⟨3417822443669927481882635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9114193183119806618353693 3417822443669927481882635)
            ·
              refine ⟨5126733665504891222823953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3417822443669927481882635 5126733665504891222823953)
              ·
                refine ⟨3845050249128668417117965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5126733665504891222823953 3845050249128668417117965)
                ·
                  refine ⟨1441893843423250656419237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3845050249128668417117965 1441893843423250656419237)
                  ·
                    refine ⟨270355095641859498078607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1441893843423250656419237 270355095641859498078607)
                    ·
                      rfl

theorem cell22_789772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 3, 4].length) (baseStart_789772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_789772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_789772 prefixEnd_789772 := by exact prefixLift 789772
  have htrace : WordTrace (prefixWord ++ tailWord_789772) baseStart_789772 baseEnd_789772 := by
    simpa [prefixWord, tailWord_789772, baseEnd_789772] using wordTrace_append hprefix tailTrace_789772
  have hstable : (prefixWord ++ tailWord_789772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789772).length < 2 ^ (prefixWord ++ tailWord_789772).sum := by decide
  have hdescent : baseEnd_789772 < baseStart_789772 := by decide
  rcases family_descends (prefixWord ++ tailWord_789772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789789 : List Nat := [1, 4, 2, 3, 1, 1, 2, 1, 3, 4]
def baseStart_789789 : Nat := 118140960795 + 789789 * 2 ^ 59
def prefixEnd_789789 : Nat := 4983230072969 + 3 ^ 40 * 789789 * 2
def baseEnd_789789 : Nat := 270360915089277120403555

theorem tailTrace_789789 : CollatzResearch.WordTrace tailWord_789789 prefixEnd_789789 270360915089277120403555 := by
  unfold tailWord_789789
  simp only [CollatzResearch.WordTrace]
  refine ⟨28805971335736813067548421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19203980890491208711698947 28805971335736813067548421)
  ·
    refine ⟨5401119625450652450165329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28805971335736813067548421 5401119625450652450165329)
    ·
      refine ⟨4050839719087989337623997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5401119625450652450165329 4050839719087989337623997)
      ·
        refine ⟨1519064894657996001608999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4050839719087989337623997 1519064894657996001608999)
        ·
          refine ⟨2278597341986994002413499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1519064894657996001608999 2278597341986994002413499)
          ·
            refine ⟨3417896012980491003620249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2278597341986994002413499 3417896012980491003620249)
            ·
              refine ⟨2563422009735368252715187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3417896012980491003620249 2563422009735368252715187)
              ·
                refine ⟨3845133014603052379072781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2563422009735368252715187 3845133014603052379072781)
                ·
                  refine ⟨1441924880476144642152293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3845133014603052379072781 1441924880476144642152293)
                  ·
                    refine ⟨270360915089277120403555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1441924880476144642152293 270360915089277120403555)
                    ·
                      rfl

theorem cell22_789789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_789789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_789789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_789789 prefixEnd_789789 := by exact prefixLift 789789
  have htrace : WordTrace (prefixWord ++ tailWord_789789) baseStart_789789 baseEnd_789789 := by
    simpa [prefixWord, tailWord_789789, baseEnd_789789] using wordTrace_append hprefix tailTrace_789789
  have hstable : (prefixWord ++ tailWord_789789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789789).length < 2 ^ (prefixWord ++ tailWord_789789).sum := by decide
  have hdescent : baseEnd_789789 < baseStart_789789 := by decide
  rcases family_descends (prefixWord ++ tailWord_789789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789821 : List Nat := [1, 4, 1, 5, 1, 1, 2, 1, 6]
def baseStart_789821 : Nat := 118140960795 + 789821 * 2 ^ 59
def prefixEnd_789821 : Nat := 4983230072969 + 3 ^ 40 * 789821 * 2
def baseEnd_789821 : Nat := 90123956447746567867819

theorem tailTrace_789821 : CollatzResearch.WordTrace tailWord_789821 prefixEnd_789821 90123956447746567867819 := by
  unfold tailWord_789821
  simp only [CollatzResearch.WordTrace]
  refine ⟨28807138471620882532713317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19204758981080588355142211 28807138471620882532713317)
  ·
    refine ⟨5401338463428915474883747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28807138471620882532713317 5401338463428915474883747)
    ·
      refine ⟨8102007695143373212325621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5401338463428915474883747 8102007695143373212325621)
      ·
        refine ⟨759563221419691238655527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8102007695143373212325621 759563221419691238655527)
        ·
          refine ⟨1139344832129536857983291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 759563221419691238655527 1139344832129536857983291)
          ·
            refine ⟨1709017248194305286974937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1139344832129536857983291 1709017248194305286974937)
            ·
              refine ⟨1281762936145728965231203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1709017248194305286974937 1281762936145728965231203)
              ·
                refine ⟨1922644404218593447846805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1281762936145728965231203 1922644404218593447846805)
                ·
                  refine ⟨90123956447746567867819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1922644404218593447846805 90123956447746567867819)
                  ·
                    rfl

theorem cell22_789821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 6].length) (baseStart_789821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_789821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_789821 prefixEnd_789821 := by exact prefixLift 789821
  have htrace : WordTrace (prefixWord ++ tailWord_789821) baseStart_789821 baseEnd_789821 := by
    simpa [prefixWord, tailWord_789821, baseEnd_789821] using wordTrace_append hprefix tailTrace_789821
  have hstable : (prefixWord ++ tailWord_789821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789821).length < 2 ^ (prefixWord ++ tailWord_789821).sum := by decide
  have hdescent : baseEnd_789821 < baseStart_789821 := by decide
  rcases family_descends (prefixWord ++ tailWord_789821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789866 : List Nat := [3, 1, 3, 3, 3, 1, 8]
def baseStart_789866 : Nat := 118140960795 + 789866 * 2 ^ 59
def prefixEnd_789866 : Nat := 4983230072969 + 3 ^ 40 * 789866 * 2
def baseEnd_789866 : Nat := 10014343472699058749197

theorem tailTrace_789866 : CollatzResearch.WordTrace tailWord_789866 prefixEnd_789866 10014343472699058749197 := by
  unfold tailWord_789866
  simp only [CollatzResearch.WordTrace]
  refine ⟨7202194939114463804525363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19205853170971903478734301 7202194939114463804525363)
  ·
    refine ⟨10803292408671695706788045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7202194939114463804525363 10803292408671695706788045)
    ·
      refine ⟨4051234653251885890045517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10803292408671695706788045 4051234653251885890045517)
      ·
        refine ⟨1519212994969457208767069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4051234653251885890045517 1519212994969457208767069)
        ·
          refine ⟨569704873113546453287651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1519212994969457208767069 569704873113546453287651)
          ·
            refine ⟨854557309670319679931477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 569704873113546453287651 854557309670319679931477)
            ·
              refine ⟨10014343472699058749197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 854557309670319679931477 10014343472699058749197)
              ·
                rfl

theorem cell22_789866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 8].length) (baseStart_789866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_789866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_789866 prefixEnd_789866 := by exact prefixLift 789866
  have htrace : WordTrace (prefixWord ++ tailWord_789866) baseStart_789866 baseEnd_789866 := by
    simpa [prefixWord, tailWord_789866, baseEnd_789866] using wordTrace_append hprefix tailTrace_789866
  have hstable : (prefixWord ++ tailWord_789866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789866).length < 2 ^ (prefixWord ++ tailWord_789866).sum := by decide
  have hdescent : baseEnd_789866 < baseStart_789866 := by decide
  rcases family_descends (prefixWord ++ tailWord_789866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789881 : List Nat := [1, 2, 1, 3, 2, 1, 2, 6, 1, 3]
def baseStart_789881 : Nat := 118140960795 + 789881 * 2 ^ 59
def prefixEnd_789881 : Nat := 4983230072969 + 3 ^ 40 * 789881 * 2
def baseEnd_789881 : Nat := 270392408569419547103273

theorem tailTrace_789881 : CollatzResearch.WordTrace tailWord_789881 prefixEnd_789881 270392408569419547103273 := by
  unfold tailWord_789881
  simp only [CollatzResearch.WordTrace]
  refine ⟨28809326851403512779897497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19206217900935675186598331 28809326851403512779897497)
  ·
    refine ⟨21606995138552634584923123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28809326851403512779897497 21606995138552634584923123)
    ·
      refine ⟨32410492707828951877384685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21606995138552634584923123 32410492707828951877384685)
      ·
        refine ⟨12153934765435856954019257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32410492707828951877384685 12153934765435856954019257)
        ·
          refine ⟨9115451074076892715514443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12153934765435856954019257 9115451074076892715514443)
          ·
            refine ⟨13673176611115339073271665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9115451074076892715514443 13673176611115339073271665)
            ·
              refine ⟨10254882458336504304953749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13673176611115339073271665 10254882458336504304953749)
              ·
                refine ⟨480697615234523639294707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10254882458336504304953749 480697615234523639294707)
                ·
                  refine ⟨721046422851785458942061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 480697615234523639294707 721046422851785458942061)
                  ·
                    refine ⟨270392408569419547103273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 721046422851785458942061 270392408569419547103273)
                    ·
                      rfl

theorem cell22_789881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 6, 1, 3].length) (baseStart_789881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_789881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_789881 prefixEnd_789881 := by exact prefixLift 789881
  have htrace : WordTrace (prefixWord ++ tailWord_789881) baseStart_789881 baseEnd_789881 := by
    simpa [prefixWord, tailWord_789881, baseEnd_789881] using wordTrace_append hprefix tailTrace_789881
  have hstable : (prefixWord ++ tailWord_789881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789881).length < 2 ^ (prefixWord ++ tailWord_789881).sum := by decide
  have hdescent : baseEnd_789881 < baseStart_789881 := by decide
  rcases family_descends (prefixWord ++ tailWord_789881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789928 : List Nat := [2, 1, 6, 1, 2, 1, 2, 2, 5]
def baseStart_789928 : Nat := 118140960795 + 789928 * 2 ^ 59
def prefixEnd_789928 : Nat := 4983230072969 + 3 ^ 40 * 789928 * 2
def baseEnd_789928 : Nat := 90136165876642363726043

theorem tailTrace_789928 : CollatzResearch.WordTrace tailWord_789928 prefixEnd_789928 90136165876642363726043 := by
  unfold tailWord_789928
  simp only [CollatzResearch.WordTrace]
  refine ⟨14405520541116619903429219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19207360721488826537905625 14405520541116619903429219)
  ·
    refine ⟨21608280811674929855143829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14405520541116619903429219 21608280811674929855143829)
    ·
      refine ⟨1012888163047262336959867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 21608280811674929855143829 1012888163047262336959867)
      ·
        refine ⟨1519332244570893505439801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1012888163047262336959867 1519332244570893505439801)
        ·
          refine ⟨1139499183428170129079851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1519332244570893505439801 1139499183428170129079851)
          ·
            refine ⟨1709248775142255193619777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1139499183428170129079851 1709248775142255193619777)
            ·
              refine ⟨1281936581356691395214833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1709248775142255193619777 1281936581356691395214833)
              ·
                refine ⟨961452436017518546411125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1281936581356691395214833 961452436017518546411125)
                ·
                  refine ⟨90136165876642363726043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 961452436017518546411125 90136165876642363726043)
                  ·
                    rfl

theorem cell22_789928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 2, 5].length) (baseStart_789928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_789928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_789928 prefixEnd_789928 := by exact prefixLift 789928
  have htrace : WordTrace (prefixWord ++ tailWord_789928) baseStart_789928 baseEnd_789928 := by
    simpa [prefixWord, tailWord_789928, baseEnd_789928] using wordTrace_append hprefix tailTrace_789928
  have hstable : (prefixWord ++ tailWord_789928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789928).length < 2 ^ (prefixWord ++ tailWord_789928).sum := by decide
  have hdescent : baseEnd_789928 < baseStart_789928 := by decide
  rcases family_descends (prefixWord ++ tailWord_789928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789956 : List Nat := [2, 3, 3, 2, 1, 2, 1, 2, 6]
def baseStart_789956 : Nat := 118140960795 + 789956 * 2 ^ 59
def prefixEnd_789956 : Nat := 4983230072969 + 3 ^ 40 * 789956 * 2
def baseEnd_789956 : Nat := 90139360867381450492681

theorem tailTrace_789956 : CollatzResearch.WordTrace tailWord_789956 prefixEnd_789956 90139360867381450492681 := by
  unfold tailWord_789956
  simp only [CollatzResearch.WordTrace]
  refine ⟨14406031163065900294438861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19208041550754533725918481 14406031163065900294438861)
  ·
    refine ⟨5402261686149712610414573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14406031163065900294438861 5402261686149712610414573)
    ·
      refine ⟨2025848132306142228905465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5402261686149712610414573 2025848132306142228905465)
      ·
        refine ⟨1519386099229606671679099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2025848132306142228905465 1519386099229606671679099)
        ·
          refine ⟨2279079148844410007518649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1519386099229606671679099 2279079148844410007518649)
          ·
            refine ⟨1709309361633307505638987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2279079148844410007518649 1709309361633307505638987)
            ·
              refine ⟨2563964042449961258458481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1709309361633307505638987 2563964042449961258458481)
              ·
                refine ⟨1922973031837470943843861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2563964042449961258458481 1922973031837470943843861)
                ·
                  refine ⟨90139360867381450492681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1922973031837470943843861 90139360867381450492681)
                  ·
                    rfl

theorem cell22_789956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 6].length) (baseStart_789956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_789956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_789956 prefixEnd_789956 := by exact prefixLift 789956
  have htrace : WordTrace (prefixWord ++ tailWord_789956) baseStart_789956 baseEnd_789956 := by
    simpa [prefixWord, tailWord_789956, baseEnd_789956] using wordTrace_append hprefix tailTrace_789956
  have hstable : (prefixWord ++ tailWord_789956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789956).length < 2 ^ (prefixWord ++ tailWord_789956).sum := by decide
  have hdescent : baseEnd_789956 < baseStart_789956 := by decide
  rcases family_descends (prefixWord ++ tailWord_789956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789967 : List Nat := [1, 1, 2, 1, 1, 4, 2, 10]
def baseStart_789967 : Nat := 118140960795 + 789967 * 2 ^ 59
def prefixEnd_789967 : Nat := 4983230072969 + 3 ^ 40 * 789967 * 2
def baseEnd_789967 : Nat := 30046872014104887717001

theorem tailTrace_789967 : CollatzResearch.WordTrace tailWord_789967 prefixEnd_789967 30046872014104887717001 := by
  unfold tailWord_789967
  simp only [CollatzResearch.WordTrace]
  refine ⟨28812463529091949467528155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19208309019394632978352103 28812463529091949467528155)
  ·
    refine ⟨43218695293637924201292233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28812463529091949467528155 43218695293637924201292233)
    ·
      refine ⟨32414021470228443150969175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43218695293637924201292233 32414021470228443150969175)
      ·
        refine ⟨48621032205342664726453763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32414021470228443150969175 48621032205342664726453763)
        ·
          refine ⟨72931548308013997089680645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48621032205342664726453763 72931548308013997089680645)
          ·
            refine ⟨13674665307752624454315121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72931548308013997089680645 13674665307752624454315121)
            ·
              refine ⟨10255998980814468340736341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13674665307752624454315121 10255998980814468340736341)
              ·
                refine ⟨30046872014104887717001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 10255998980814468340736341 30046872014104887717001)
                ·
                  rfl

theorem cell22_789967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 10].length) (baseStart_789967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_789967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_789967 prefixEnd_789967 := by exact prefixLift 789967
  have htrace : WordTrace (prefixWord ++ tailWord_789967) baseStart_789967 baseEnd_789967 := by
    simpa [prefixWord, tailWord_789967, baseEnd_789967] using wordTrace_append hprefix tailTrace_789967
  have hstable : (prefixWord ++ tailWord_789967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789967).length < 2 ^ (prefixWord ++ tailWord_789967).sum := by decide
  have hdescent : baseEnd_789967 < baseStart_789967 := by decide
  rcases family_descends (prefixWord ++ tailWord_789967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790018 : List Nat := [3, 4, 1, 2, 1, 1, 4, 6]
def baseStart_790018 : Nat := 118140960795 + 790018 * 2 ^ 59
def prefixEnd_790018 : Nat := 4983230072969 + 3 ^ 40 * 790018 * 2
def baseEnd_790018 : Nat := 30048811829910761825317

theorem tailTrace_790018 : CollatzResearch.WordTrace tailWord_790018 prefixEnd_790018 30048811829910761825317 := by
  unfold tailWord_790018
  simp only [CollatzResearch.WordTrace]
  refine ⟨7203580912976796294408677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19209549101271456785089805 7203580912976796294408677)
  ·
    refine ⟨1350671421183149305201627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7203580912976796294408677 1350671421183149305201627)
    ·
      refine ⟨2026007131774723957802441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1350671421183149305201627 2026007131774723957802441)
      ·
        refine ⟨1519505348831042968351831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2026007131774723957802441 1519505348831042968351831)
        ·
          refine ⟨2279258023246564452527747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1519505348831042968351831 2279258023246564452527747)
          ·
            refine ⟨3418887034869846678791621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2279258023246564452527747 3418887034869846678791621)
            ·
              refine ⟨641041319038096252273429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3418887034869846678791621 641041319038096252273429)
              ·
                refine ⟨30048811829910761825317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 641041319038096252273429 30048811829910761825317)
                ·
                  rfl

theorem cell22_790018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 6].length) (baseStart_790018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_790018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_790018 prefixEnd_790018 := by exact prefixLift 790018
  have htrace : WordTrace (prefixWord ++ tailWord_790018) baseStart_790018 baseEnd_790018 := by
    simpa [prefixWord, tailWord_790018, baseEnd_790018] using wordTrace_append hprefix tailTrace_790018
  have hstable : (prefixWord ++ tailWord_790018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790018).length < 2 ^ (prefixWord ++ tailWord_790018).sum := by decide
  have hdescent : baseEnd_790018 < baseStart_790018 := by decide
  rcases family_descends (prefixWord ++ tailWord_790018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790074 : List Nat := [3, 1, 1, 1, 3, 2, 2, 1, 8]
def baseStart_790074 : Nat := 118140960795 + 790074 * 2 ^ 59
def prefixEnd_790074 : Nat := 4983230072969 + 3 ^ 40 * 790074 * 2
def baseEnd_790074 : Nat := 90152825471210459009227

theorem tailTrace_790074 : CollatzResearch.WordTrace tailWord_790074 prefixEnd_790074 90152825471210459009227 := by
  unfold tailWord_790074
  simp only [CollatzResearch.WordTrace]
  refine ⟨7204091534926076685418319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19210910759802871161115517 7204091534926076685418319)
  ·
    refine ⟨10806137302389115028127479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7204091534926076685418319 10806137302389115028127479)
    ·
      refine ⟨16209205953583672542191219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10806137302389115028127479 16209205953583672542191219)
      ·
        refine ⟨24313808930375508813286829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16209205953583672542191219 24313808930375508813286829)
        ·
          refine ⟨9117678348890815804982561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24313808930375508813286829 9117678348890815804982561)
          ·
            refine ⟨6838258761668111853736921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9117678348890815804982561 6838258761668111853736921)
            ·
              refine ⟨5128694071251083890302691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6838258761668111853736921 5128694071251083890302691)
              ·
                refine ⟨7693041106876625835454037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5128694071251083890302691 7693041106876625835454037)
                ·
                  refine ⟨90152825471210459009227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7693041106876625835454037 90152825471210459009227)
                  ·
                    rfl

theorem cell22_790074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 8].length) (baseStart_790074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_790074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_790074 prefixEnd_790074 := by exact prefixLift 790074
  have htrace : WordTrace (prefixWord ++ tailWord_790074) baseStart_790074 baseEnd_790074 := by
    simpa [prefixWord, tailWord_790074, baseEnd_790074] using wordTrace_append hprefix tailTrace_790074
  have hstable : (prefixWord ++ tailWord_790074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790074).length < 2 ^ (prefixWord ++ tailWord_790074).sum := by decide
  have hdescent : baseEnd_790074 < baseStart_790074 := by decide
  rcases family_descends (prefixWord ++ tailWord_790074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790091 : List Nat := [1, 1, 1, 1, 3, 1, 3, 7, 4]
def baseStart_790091 : Nat := 118140960795 + 790091 * 2 ^ 59
def prefixEnd_790091 : Nat := 4983230072969 + 3 ^ 40 * 790091 * 2
def baseEnd_790091 : Nat := 90154765287016333117543

theorem tailTrace_790091 : CollatzResearch.WordTrace tailWord_790091 prefixEnd_790091 90154765287016333117543 := by
  unfold tailWord_790091
  simp only [CollatzResearch.WordTrace]
  refine ⟨28816986180642718645042127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19211324120428479096694751 28816986180642718645042127)
  ·
    refine ⟨43225479270964077967563191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28816986180642718645042127 43225479270964077967563191)
    ·
      refine ⟨64838218906446116951344787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43225479270964077967563191 64838218906446116951344787)
      ·
        refine ⟨97257328359669175427017181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64838218906446116951344787 97257328359669175427017181)
        ·
          refine ⟨36471498134875940785131443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97257328359669175427017181 36471498134875940785131443)
          ·
            refine ⟨54707247202313911177697165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36471498134875940785131443 54707247202313911177697165)
            ·
              refine ⟨20515217700867716691636437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54707247202313911177697165 20515217700867716691636437)
              ·
                refine ⟨480825414864087109960229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 20515217700867716691636437 480825414864087109960229)
                ·
                  refine ⟨90154765287016333117543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 480825414864087109960229 90154765287016333117543)
                  ·
                    rfl

theorem cell22_790091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 7, 4].length) (baseStart_790091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_790091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_790091 prefixEnd_790091 := by exact prefixLift 790091
  have htrace : WordTrace (prefixWord ++ tailWord_790091) baseStart_790091 baseEnd_790091 := by
    simpa [prefixWord, tailWord_790091, baseEnd_790091] using wordTrace_append hprefix tailTrace_790091
  have hstable : (prefixWord ++ tailWord_790091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790091).length < 2 ^ (prefixWord ++ tailWord_790091).sum := by decide
  have hdescent : baseEnd_790091 < baseStart_790091 := by decide
  rcases family_descends (prefixWord ++ tailWord_790091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790104 : List Nat := [2, 1, 2, 2, 1, 2, 1, 2, 3, 6]
def baseStart_790104 : Nat := 118140960795 + 790104 * 2 ^ 59
def prefixEnd_790104 : Nat := 4983230072969 + 3 ^ 40 * 790104 * 2
def baseEnd_790104 : Nat := 270468746026721298777589

theorem tailTrace_790104 : CollatzResearch.WordTrace tailWord_790104 prefixEnd_790104 270468746026721298777589 := by
  unfold tailWord_790104
  simp only [CollatzResearch.WordTrace]
  refine ⟨14408730164797810932632683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19211640219730414576843577 14408730164797810932632683)
  ·
    refine ⟨21613095247196716398949025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14408730164797810932632683 21613095247196716398949025)
    ·
      refine ⟨16209821435397537299211769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21613095247196716398949025 16209821435397537299211769)
      ·
        refine ⟨12157366076548152974408827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16209821435397537299211769 12157366076548152974408827)
        ·
          refine ⟨18236049114822229461613241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12157366076548152974408827 18236049114822229461613241)
          ·
            refine ⟨13677036836116672096209931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18236049114822229461613241 13677036836116672096209931)
            ·
              refine ⟨20515555254175008144314897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13677036836116672096209931 20515555254175008144314897)
              ·
                refine ⟨15386666440631256108236173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20515555254175008144314897 15386666440631256108236173)
                ·
                  refine ⟨5769999915236721040588565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15386666440631256108236173 5769999915236721040588565)
                  ·
                    refine ⟨270468746026721298777589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5769999915236721040588565 270468746026721298777589)
                    ·
                      rfl

theorem cell22_790104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 3, 6].length) (baseStart_790104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_790104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_790104 prefixEnd_790104 := by exact prefixLift 790104
  have htrace : WordTrace (prefixWord ++ tailWord_790104) baseStart_790104 baseEnd_790104 := by
    simpa [prefixWord, tailWord_790104, baseEnd_790104] using wordTrace_append hprefix tailTrace_790104
  have hstable : (prefixWord ++ tailWord_790104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790104).length < 2 ^ (prefixWord ++ tailWord_790104).sum := by decide
  have hdescent : baseEnd_790104 < baseStart_790104 := by decide
  rcases family_descends (prefixWord ++ tailWord_790104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790106 : List Nat := [3, 1, 1, 2, 1, 1, 1, 5, 4, 3]
def baseStart_790106 : Nat := 118140960795 + 790106 * 2 ^ 59
def prefixEnd_790106 : Nat := 4983230072969 + 3 ^ 40 * 790106 * 2
def baseEnd_790106 : Nat := 270469430667593960227583

theorem tailTrace_790106 : CollatzResearch.WordTrace tailWord_790106 prefixEnd_790106 270469430667593960227583 := by
  unfold tailWord_790106
  simp only [CollatzResearch.WordTrace]
  refine ⟨7204383318897094051709543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19211688850392250804558781 7204383318897094051709543)
  ·
    refine ⟨10806574978345641077564315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7204383318897094051709543 10806574978345641077564315)
    ·
      refine ⟨16209862467518461616346473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10806574978345641077564315 16209862467518461616346473)
      ·
        refine ⟨12157396850638846212259855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16209862467518461616346473 12157396850638846212259855)
        ·
          refine ⟨18236095275958269318389783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12157396850638846212259855 18236095275958269318389783)
          ·
            refine ⟨27354142913937403977584675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18236095275958269318389783 27354142913937403977584675)
            ·
              refine ⟨41031214370906105966377013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27354142913937403977584675 41031214370906105966377013)
              ·
                refine ⟨3846676347272447434347845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41031214370906105966377013 3846676347272447434347845)
                ·
                  refine ⟨721251815113583893940221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3846676347272447434347845 721251815113583893940221)
                  ·
                    refine ⟨270469430667593960227583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 721251815113583893940221 270469430667593960227583)
                    ·
                      rfl

theorem cell22_790106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 4, 3].length) (baseStart_790106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_790106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_790106 prefixEnd_790106 := by exact prefixLift 790106
  have htrace : WordTrace (prefixWord ++ tailWord_790106) baseStart_790106 baseEnd_790106 := by
    simpa [prefixWord, tailWord_790106, baseEnd_790106] using wordTrace_append hprefix tailTrace_790106
  have hstable : (prefixWord ++ tailWord_790106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790106).length < 2 ^ (prefixWord ++ tailWord_790106).sum := by decide
  have hdescent : baseEnd_790106 < baseStart_790106 := by decide
  rcases family_descends (prefixWord ++ tailWord_790106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790168 : List Nat := [2, 1, 2, 4, 1, 2, 1, 3, 3, 3]
def baseStart_790168 : Nat := 118140960795 + 790168 * 2 ^ 59
def prefixEnd_790168 : Nat := 4983230072969 + 3 ^ 40 * 790168 * 2
def baseEnd_790168 : Nat := 270490654534646465177393

theorem tailTrace_790168 : CollatzResearch.WordTrace tailWord_790168 prefixEnd_790168 270490654534646465177393 := by
  unfold tailWord_790168
  simp only [CollatzResearch.WordTrace]
  refine ⟨14409897300681880397797579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19213196400909173863730105 14409897300681880397797579)
  ·
    refine ⟨21614845951022820596696369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14409897300681880397797579 21614845951022820596696369)
    ·
      refine ⟨16211134463267115447522277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21614845951022820596696369 16211134463267115447522277)
      ·
        refine ⟨3039587711862584146410427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16211134463267115447522277 3039587711862584146410427)
        ·
          refine ⟨4559381567793876219615641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3039587711862584146410427 4559381567793876219615641)
          ·
            refine ⟨3419536175845407164711731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4559381567793876219615641 3419536175845407164711731)
            ·
              refine ⟨5129304263768110747067597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3419536175845407164711731 5129304263768110747067597)
              ·
                refine ⟨1923489098913041530150349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5129304263768110747067597 1923489098913041530150349)
                ·
                  refine ⟨721308412092390573806381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1923489098913041530150349 721308412092390573806381)
                  ·
                    refine ⟨270490654534646465177393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 721308412092390573806381 270490654534646465177393)
                    ·
                      rfl

theorem cell22_790168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 3, 3].length) (baseStart_790168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_790168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_790168 prefixEnd_790168 := by exact prefixLift 790168
  have htrace : WordTrace (prefixWord ++ tailWord_790168) baseStart_790168 baseEnd_790168 := by
    simpa [prefixWord, tailWord_790168, baseEnd_790168] using wordTrace_append hprefix tailTrace_790168
  have hstable : (prefixWord ++ tailWord_790168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790168).length < 2 ^ (prefixWord ++ tailWord_790168).sum := by decide
  have hdescent : baseEnd_790168 < baseStart_790168 := by decide
  rcases family_descends (prefixWord ++ tailWord_790168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790181 : List Nat := [1, 3, 1, 2, 1, 2, 2, 5, 5]
def baseStart_790181 : Nat := 118140960795 + 790181 * 2 ^ 59
def prefixEnd_790181 : Nat := 4983230072969 + 3 ^ 40 * 790181 * 2
def baseEnd_790181 : Nat := 90165034900106254867451

theorem tailTrace_790181 : CollatzResearch.WordTrace tailWord_790181 prefixEnd_790181 90165034900106254867451 := by
  unfold tailWord_790181
  simp only [CollatzResearch.WordTrace]
  refine ⟨28820268750316664015818397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19213512500211109343878931 28820268750316664015818397)
  ·
    refine ⟨10807600781368749005931899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28820268750316664015818397 10807600781368749005931899)
    ·
      refine ⟨16211401172053123508897849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10807600781368749005931899 16211401172053123508897849)
      ·
        refine ⟨12158550879039842631673387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16211401172053123508897849 12158550879039842631673387)
        ·
          refine ⟨18237826318559763947510081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12158550879039842631673387 18237826318559763947510081)
          ·
            refine ⟨13678369738919822960632561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18237826318559763947510081 13678369738919822960632561)
            ·
              refine ⟨10258777304189867220474421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13678369738919822960632561 10258777304189867220474421)
              ·
                refine ⟨961760372267800051919477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10258777304189867220474421 961760372267800051919477)
                ·
                  refine ⟨90165034900106254867451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 961760372267800051919477 90165034900106254867451)
                  ·
                    rfl

theorem cell22_790181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 5, 5].length) (baseStart_790181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_790181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_790181 prefixEnd_790181 := by exact prefixLift 790181
  have htrace : WordTrace (prefixWord ++ tailWord_790181) baseStart_790181 baseEnd_790181 := by
    simpa [prefixWord, tailWord_790181, baseEnd_790181] using wordTrace_append hprefix tailTrace_790181
  have hstable : (prefixWord ++ tailWord_790181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790181).length < 2 ^ (prefixWord ++ tailWord_790181).sum := by decide
  have hdescent : baseEnd_790181 < baseStart_790181 := by decide
  rcases family_descends (prefixWord ++ tailWord_790181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790202 : List Nat := [3, 1, 1, 1, 2, 6, 1, 3, 1, 3]
def baseStart_790202 : Nat := 118140960795 + 790202 * 2 ^ 59
def prefixEnd_790202 : Nat := 4983230072969 + 3 ^ 40 * 790202 * 2
def baseEnd_790202 : Nat := 270502293429481709827289

theorem tailTrace_790202 : CollatzResearch.WordTrace tailWord_790202 prefixEnd_790202 270502293429481709827289 := by
  unfold tailWord_790202
  simp only [CollatzResearch.WordTrace]
  refine ⟨7205258670810146150583215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19214023122160389734888573 7205258670810146150583215)
  ·
    refine ⟨10807888006215219225874823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7205258670810146150583215 10807888006215219225874823)
    ·
      refine ⟨16211832009322828838812235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10807888006215219225874823 16211832009322828838812235)
      ·
        refine ⟨24317748013984243258218353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16211832009322828838812235 24317748013984243258218353)
        ·
          refine ⟨18238311010488182443663765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24317748013984243258218353 18238311010488182443663765)
          ·
            refine ⟨854920828616633552046739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 18238311010488182443663765 854920828616633552046739)
            ·
              refine ⟨1282381242924950328070109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 854920828616633552046739 1282381242924950328070109)
              ·
                refine ⟨480892966096856373026291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1282381242924950328070109 480892966096856373026291)
                ·
                  refine ⟨721339449145284559539437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 480892966096856373026291 721339449145284559539437)
                  ·
                    refine ⟨270502293429481709827289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 721339449145284559539437 270502293429481709827289)
                    ·
                      rfl

theorem cell22_790202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 3, 1, 3].length) (baseStart_790202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_790202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_790202 prefixEnd_790202 := by exact prefixLift 790202
  have htrace : WordTrace (prefixWord ++ tailWord_790202) baseStart_790202 baseEnd_790202 := by
    simpa [prefixWord, tailWord_790202, baseEnd_790202] using wordTrace_append hprefix tailTrace_790202
  have hstable : (prefixWord ++ tailWord_790202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790202).length < 2 ^ (prefixWord ++ tailWord_790202).sum := by decide
  have hdescent : baseEnd_790202 < baseStart_790202 := by decide
  rcases family_descends (prefixWord ++ tailWord_790202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790258 : List Nat := [3, 2, 1, 3, 1, 1, 3, 2, 1, 5]
def baseStart_790258 : Nat := 118140960795 + 790258 * 2 ^ 59
def prefixEnd_790258 : Nat := 4983230072969 + 3 ^ 40 * 790258 * 2
def baseEnd_790258 : Nat := 270521463373916230427117

theorem tailTrace_790258 : CollatzResearch.WordTrace tailWord_790258 prefixEnd_790258 270521463373916230427117 := by
  unfold tailWord_790258
  simp only [CollatzResearch.WordTrace]
  refine ⟨7205769292759426541592857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19215384780691804110914285 7205769292759426541592857)
  ·
    refine ⟨5404326969569569906194643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7205769292759426541592857 5404326969569569906194643)
    ·
      refine ⟨8106490454354354859291965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5404326969569569906194643 8106490454354354859291965)
      ·
        refine ⟨3039933920382883072234487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8106490454354354859291965 3039933920382883072234487)
        ·
          refine ⟨4559900880574324608351731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3039933920382883072234487 4559900880574324608351731)
          ·
            refine ⟨6839851320861486912527597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4559900880574324608351731 6839851320861486912527597)
            ·
              refine ⟨2564944245323057592197849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6839851320861486912527597 2564944245323057592197849)
              ·
                refine ⟨1923708183992293194148387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2564944245323057592197849 1923708183992293194148387)
                ·
                  refine ⟨2885562275988439791222581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1923708183992293194148387 2885562275988439791222581)
                  ·
                    refine ⟨270521463373916230427117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2885562275988439791222581 270521463373916230427117)
                    ·
                      rfl

theorem cell22_790258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_790258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_790258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_790258 prefixEnd_790258 := by exact prefixLift 790258
  have htrace : WordTrace (prefixWord ++ tailWord_790258) baseStart_790258 baseEnd_790258 := by
    simpa [prefixWord, tailWord_790258, baseEnd_790258] using wordTrace_append hprefix tailTrace_790258
  have hstable : (prefixWord ++ tailWord_790258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790258).length < 2 ^ (prefixWord ++ tailWord_790258).sum := by decide
  have hdescent : baseEnd_790258 < baseStart_790258 := by decide
  rcases family_descends (prefixWord ++ tailWord_790258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790262 : List Nat := [5, 1, 1, 1, 1, 4, 3, 1, 1, 4]
def baseStart_790262 : Nat := 118140960795 + 790262 * 2 ^ 59
def prefixEnd_790262 : Nat := 4983230072969 + 3 ^ 40 * 790262 * 2
def baseEnd_790262 : Nat := 270522832655661553327105

theorem tailTrace_790262 : CollatzResearch.WordTrace tailWord_790262 prefixEnd_790262 270522832655661553327105 := by
  unfold tailWord_790262
  simp only [CollatzResearch.WordTrace]
  refine ⟨1801451441438950928094815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19215482042015476566344693 1801451441438950928094815)
  ·
    refine ⟨2702177162158426392142223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1801451441438950928094815 2702177162158426392142223)
    ·
      refine ⟨4053265743237639588213335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2702177162158426392142223 4053265743237639588213335)
      ·
        refine ⟨6079898614856459382320003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4053265743237639588213335 6079898614856459382320003)
        ·
          refine ⟨9119847922284689073480005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6079898614856459382320003 9119847922284689073480005)
          ·
            refine ⟨1709971485428379201277501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9119847922284689073480005 1709971485428379201277501)
            ·
              refine ⟨641239307035642200479063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1709971485428379201277501 641239307035642200479063)
              ·
                refine ⟨961858960553463300718595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 641239307035642200479063 961858960553463300718595)
                ·
                  refine ⟨1442788440830194951077893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 961858960553463300718595 1442788440830194951077893)
                  ·
                    refine ⟨270522832655661553327105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1442788440830194951077893 270522832655661553327105)
                    ·
                      rfl

theorem cell22_790262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_790262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_790262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_790262 prefixEnd_790262 := by exact prefixLift 790262
  have htrace : WordTrace (prefixWord ++ tailWord_790262) baseStart_790262 baseEnd_790262 := by
    simpa [prefixWord, tailWord_790262, baseEnd_790262] using wordTrace_append hprefix tailTrace_790262
  have hstable : (prefixWord ++ tailWord_790262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790262).length < 2 ^ (prefixWord ++ tailWord_790262).sum := by decide
  have hdescent : baseEnd_790262 < baseStart_790262 := by decide
  rcases family_descends (prefixWord ++ tailWord_790262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790273 : List Nat := [1, 2, 4, 1, 1, 1, 4, 2, 2, 4]
def baseStart_790273 : Nat := 118140960795 + 790273 * 2 ^ 59
def prefixEnd_790273 : Nat := 4983230072969 + 3 ^ 40 * 790273 * 2
def baseEnd_790273 : Nat := 270526598180461191302071

theorem tailTrace_790273 : CollatzResearch.WordTrace tailWord_790273 prefixEnd_790273 270526598180461191302071 := by
  unfold tailWord_790273
  simp only [CollatzResearch.WordTrace]
  refine ⟨28823624265983363728167473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19215749510655575818778315 28823624265983363728167473)
  ·
    refine ⟨21617718199487522796125605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28823624265983363728167473 21617718199487522796125605)
    ·
      refine ⟨4053322162403910524273551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21617718199487522796125605 4053322162403910524273551)
      ·
        refine ⟨6079983243605865786410327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4053322162403910524273551 6079983243605865786410327)
        ·
          refine ⟨9119974865408798679615491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6079983243605865786410327 9119974865408798679615491)
          ·
            refine ⟨13679962298113198019423237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9119974865408798679615491 13679962298113198019423237)
            ·
              refine ⟨2564992930896224628641857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13679962298113198019423237 2564992930896224628641857)
              ·
                refine ⟨1923744698172168471481393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2564992930896224628641857 1923744698172168471481393)
                ·
                  refine ⟨1442808523629126353611045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1923744698172168471481393 1442808523629126353611045)
                  ·
                    refine ⟨270526598180461191302071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1442808523629126353611045 270526598180461191302071)
                    ·
                      rfl

theorem cell22_790273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_790273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_790273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_790273 prefixEnd_790273 := by exact prefixLift 790273
  have htrace : WordTrace (prefixWord ++ tailWord_790273) baseStart_790273 baseEnd_790273 := by
    simpa [prefixWord, tailWord_790273, baseEnd_790273] using wordTrace_append hprefix tailTrace_790273
  have hstable : (prefixWord ++ tailWord_790273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790273).length < 2 ^ (prefixWord ++ tailWord_790273).sum := by decide
  have hdescent : baseEnd_790273 < baseStart_790273 := by decide
  rcases family_descends (prefixWord ++ tailWord_790273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790371 : List Nat := [1, 1, 1, 5, 5, 1, 1, 3, 1, 3]
def baseStart_790371 : Nat := 118140960795 + 790371 * 2 ^ 59
def prefixEnd_790371 : Nat := 4983230072969 + 3 ^ 40 * 790371 * 2
def baseEnd_790371 : Nat := 270560145583221602351771

theorem tailTrace_790371 : CollatzResearch.WordTrace tailWord_790371 prefixEnd_790371 270560145583221602351771 := by
  unfold tailWord_790371
  simp only [CollatzResearch.WordTrace]
  refine ⟨28827198619628326465234967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19218132413085550976823311 28827198619628326465234967)
  ·
    refine ⟨43240797929442489697852451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28827198619628326465234967 43240797929442489697852451)
    ·
      refine ⟨64861196894163734546778677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43240797929442489697852451 64861196894163734546778677)
      ·
        refine ⟨6080737208827850113760501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64861196894163734546778677 6080737208827850113760501)
        ·
          refine ⟨570069113327610948165047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6080737208827850113760501 570069113327610948165047)
          ·
            refine ⟨855103669991416422247571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 570069113327610948165047 855103669991416422247571)
            ·
              refine ⟨1282655504987124633371357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 855103669991416422247571 1282655504987124633371357)
              ·
                refine ⟨480995814370171737514259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1282655504987124633371357 480995814370171737514259)
                ·
                  refine ⟨721493721555257606271389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 480995814370171737514259 721493721555257606271389)
                  ·
                    refine ⟨270560145583221602351771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 721493721555257606271389 270560145583221602351771)
                    ·
                      rfl

theorem cell22_790371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 3, 1, 3].length) (baseStart_790371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_790371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_790371 prefixEnd_790371 := by exact prefixLift 790371
  have htrace : WordTrace (prefixWord ++ tailWord_790371) baseStart_790371 baseEnd_790371 := by
    simpa [prefixWord, tailWord_790371, baseEnd_790371] using wordTrace_append hprefix tailTrace_790371
  have hstable : (prefixWord ++ tailWord_790371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790371).length < 2 ^ (prefixWord ++ tailWord_790371).sum := by decide
  have hdescent : baseEnd_790371 < baseStart_790371 := by decide
  rcases family_descends (prefixWord ++ tailWord_790371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790380 : List Nat := [2, 2, 1, 1, 4, 2, 2, 3, 1, 4]
def baseStart_790380 : Nat := 118140960795 + 790380 * 2 ^ 59
def prefixEnd_790380 : Nat := 4983230072969 + 3 ^ 40 * 790380 * 2
def baseEnd_790380 : Nat := 270563226467148578876743

theorem tailTrace_790380 : CollatzResearch.WordTrace tailWord_790380 prefixEnd_790380 270563226467148578876743 := by
  unfold tailWord_790380
  simp only [CollatzResearch.WordTrace]
  refine ⟨14413763438297860501156297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19218351251063814001541729 14413763438297860501156297)
  ·
    refine ⟨10810322578723395375867223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14413763438297860501156297 10810322578723395375867223)
    ·
      refine ⟨16215483868085093063800835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10810322578723395375867223 16215483868085093063800835)
      ·
        refine ⟨24323225802127639595701253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16215483868085093063800835 24323225802127639595701253)
        ·
          refine ⟨4560604837898932424193985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24323225802127639595701253 4560604837898932424193985)
          ·
            refine ⟨3420453628424199318145489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4560604837898932424193985 3420453628424199318145489)
            ·
              refine ⟨2565340221318149488609117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3420453628424199318145489 2565340221318149488609117)
              ·
                refine ⟨962002582994306058228419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2565340221318149488609117 962002582994306058228419)
                ·
                  refine ⟨1443003874491459087342629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 962002582994306058228419 1443003874491459087342629)
                  ·
                    refine ⟨270563226467148578876743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1443003874491459087342629 270563226467148578876743)
                    ·
                      rfl

theorem cell22_790380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 4].length) (baseStart_790380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_790380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_790380 prefixEnd_790380 := by exact prefixLift 790380
  have htrace : WordTrace (prefixWord ++ tailWord_790380) baseStart_790380 baseEnd_790380 := by
    simpa [prefixWord, tailWord_790380, baseEnd_790380] using wordTrace_append hprefix tailTrace_790380
  have hstable : (prefixWord ++ tailWord_790380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790380).length < 2 ^ (prefixWord ++ tailWord_790380).sum := by decide
  have hdescent : baseEnd_790380 < baseStart_790380 := by decide
  rcases family_descends (prefixWord ++ tailWord_790380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790401 : List Nat := [1, 2, 4, 4, 2, 1, 2, 1, 5]
def baseStart_790401 : Nat := 118140960795 + 790401 * 2 ^ 59
def prefixEnd_790401 : Nat := 4983230072969 + 3 ^ 40 * 790401 * 2
def baseEnd_790401 : Nat := 90190138398770508033893

theorem tailTrace_790401 : CollatzResearch.WordTrace tailWord_790401 prefixEnd_790401 90190138398770508033893 := by
  unfold tailWord_790401
  simp only [CollatzResearch.WordTrace]
  refine ⟨28828292809519641588827057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19218861873013094392551371 28828292809519641588827057)
  ·
    refine ⟨21621219607139731191620293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28828292809519641588827057 21621219607139731191620293)
    ·
      refine ⟨4053978676338699598428805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21621219607139731191620293 4053978676338699598428805)
      ·
        refine ⟨760121001813506174705401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4053978676338699598428805 760121001813506174705401)
        ·
          refine ⟨570090751360129631029051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 760121001813506174705401 570090751360129631029051)
          ·
            refine ⟨855136127040194446543577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 570090751360129631029051 855136127040194446543577)
            ·
              refine ⟨641352095280145834907683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 855136127040194446543577 641352095280145834907683)
              ·
                refine ⟨962028142920218752361525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 641352095280145834907683 962028142920218752361525)
                ·
                  refine ⟨90190138398770508033893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 962028142920218752361525 90190138398770508033893)
                  ·
                    rfl

theorem cell22_790401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 1, 5].length) (baseStart_790401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_790401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_790401 prefixEnd_790401 := by exact prefixLift 790401
  have htrace : WordTrace (prefixWord ++ tailWord_790401) baseStart_790401 baseEnd_790401 := by
    simpa [prefixWord, tailWord_790401, baseEnd_790401] using wordTrace_append hprefix tailTrace_790401
  have hstable : (prefixWord ++ tailWord_790401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790401).length < 2 ^ (prefixWord ++ tailWord_790401).sum := by decide
  have hdescent : baseEnd_790401 < baseStart_790401 := by decide
  rcases family_descends (prefixWord ++ tailWord_790401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790423 : List Nat := [1, 1, 3, 3, 1, 3, 2, 8]
def baseStart_790423 : Nat := 118140960795 + 790423 * 2 ^ 59
def prefixEnd_790423 : Nat := 4983230072969 + 3 ^ 40 * 790423 * 2
def baseEnd_790423 : Nat := 30064216249545644450179

theorem tailTrace_790423 : CollatzResearch.WordTrace tailWord_790423 prefixEnd_790423 30064216249545644450179 := by
  unfold tailWord_790423
  simp only [CollatzResearch.WordTrace]
  refine ⟨28829095215439939346127923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19219396810293292897418615 28829095215439939346127923)
  ·
    refine ⟨43243642823159909019191885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28829095215439939346127923 43243642823159909019191885)
    ·
      refine ⟨16216366058684965882196957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43243642823159909019191885 16216366058684965882196957)
      ·
        refine ⟨6081137272006862205823859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16216366058684965882196957 6081137272006862205823859)
        ·
          refine ⟨9121705908010293308735789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6081137272006862205823859 9121705908010293308735789)
          ·
            refine ⟨3420639715503859990775921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9121705908010293308735789 3420639715503859990775921)
            ·
              refine ⟨2565479786627894993081941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3420639715503859990775921 2565479786627894993081941)
              ·
                refine ⟨30064216249545644450179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2565479786627894993081941 30064216249545644450179)
                ·
                  rfl

theorem cell22_790423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 8].length) (baseStart_790423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_790423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_790423 prefixEnd_790423 := by exact prefixLift 790423
  have htrace : WordTrace (prefixWord ++ tailWord_790423) baseStart_790423 baseEnd_790423 := by
    simpa [prefixWord, tailWord_790423, baseEnd_790423] using wordTrace_append hprefix tailTrace_790423
  have hstable : (prefixWord ++ tailWord_790423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790423).length < 2 ^ (prefixWord ++ tailWord_790423).sum := by decide
  have hdescent : baseEnd_790423 < baseStart_790423 := by decide
  rcases family_descends (prefixWord ++ tailWord_790423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790440 : List Nat := [2, 1, 6, 2, 11]
def baseStart_790440 : Nat := 118140960795 + 790440 * 2 ^ 59
def prefixEnd_790440 : Nat := 4983230072969 + 3 ^ 40 * 790440 * 2
def baseEnd_790440 : Nat := 1113513439067195153813

theorem tailTrace_790440 : CollatzResearch.WordTrace tailWord_790440 prefixEnd_790440 1113513439067195153813 := by
  unfold tailWord_790440
  simp only [CollatzResearch.WordTrace]
  refine ⟨14414857628189175624748387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19219810170918900832997849 14414857628189175624748387)
  ·
    refine ⟨21622286442283763437122581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14414857628189175624748387 21622286442283763437122581)
    ·
      refine ⟨1013544676982051411115121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 21622286442283763437122581 1013544676982051411115121)
      ·
        refine ⟨760158507736538558336341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1013544676982051411115121 760158507736538558336341)
        ·
          refine ⟨1113513439067195153813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 760158507736538558336341 1113513439067195153813)
          ·
            rfl

theorem cell22_790440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 11].length) (baseStart_790440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_790440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_790440 prefixEnd_790440 := by exact prefixLift 790440
  have htrace : WordTrace (prefixWord ++ tailWord_790440) baseStart_790440 baseEnd_790440 := by
    simpa [prefixWord, tailWord_790440, baseEnd_790440] using wordTrace_append hprefix tailTrace_790440
  have hstable : (prefixWord ++ tailWord_790440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790440).length < 2 ^ (prefixWord ++ tailWord_790440).sum := by decide
  have hdescent : baseEnd_790440 < baseStart_790440 := by decide
  rcases family_descends (prefixWord ++ tailWord_790440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790455 : List Nat := [1, 1, 3, 1, 3, 1, 1, 5, 3, 3]
def baseStart_790455 : Nat := 118140960795 + 790455 * 2 ^ 59
def prefixEnd_790455 : Nat := 4983230072969 + 3 ^ 40 * 790455 * 2
def baseEnd_790455 : Nat := 270588900499873383251513

theorem tailTrace_790455 : CollatzResearch.WordTrace tailWord_790455 prefixEnd_790455 270588900499873383251513 := by
  unfold tailWord_790455
  simp only [CollatzResearch.WordTrace]
  refine ⟨28830262351324008811292819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19220174900882672540861879 28830262351324008811292819)
  ·
    refine ⟨43245393526986013216939229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28830262351324008811292819 43245393526986013216939229)
    ·
      refine ⟨16217022572619754956352211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43245393526986013216939229 16217022572619754956352211)
      ·
        refine ⟨24325533858929632434528317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16217022572619754956352211 24325533858929632434528317)
        ·
          refine ⟨9122075197098612162948119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24325533858929632434528317 9122075197098612162948119)
          ·
            refine ⟨13683112795647918244422179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9122075197098612162948119 13683112795647918244422179)
            ·
              refine ⟨20524669193471877366633269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13683112795647918244422179 20524669193471877366633269)
              ·
                refine ⟨1924187736887988503121869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20524669193471877366633269 1924187736887988503121869)
                ·
                  refine ⟨721570401332995688670701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1924187736887988503121869 721570401332995688670701)
                  ·
                    refine ⟨270588900499873383251513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 721570401332995688670701 270588900499873383251513)
                    ·
                      rfl

theorem cell22_790455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 3, 3].length) (baseStart_790455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_790455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_790455 prefixEnd_790455 := by exact prefixLift 790455
  have htrace : WordTrace (prefixWord ++ tailWord_790455) baseStart_790455 baseEnd_790455 := by
    simpa [prefixWord, tailWord_790455, baseEnd_790455] using wordTrace_append hprefix tailTrace_790455
  have hstable : (prefixWord ++ tailWord_790455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790455).length < 2 ^ (prefixWord ++ tailWord_790455).sum := by decide
  have hdescent : baseEnd_790455 < baseStart_790455 := by decide
  rcases family_descends (prefixWord ++ tailWord_790455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790472 : List Nat := [2, 1, 3, 1, 4, 2, 1, 2, 3, 3]
def baseStart_790472 : Nat := 118140960795 + 790472 * 2 ^ 59
def prefixEnd_790472 : Nat := 4983230072969 + 3 ^ 40 * 790472 * 2
def baseEnd_790472 : Nat := 270594719947291005576461

theorem tailTrace_790472 : CollatzResearch.WordTrace tailWord_790472 prefixEnd_790472 270594719947291005576461 := by
  unfold tailWord_790472
  simp only [CollatzResearch.WordTrace]
  refine ⟨14415441196131210357330835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19220588261508280476441113 14415441196131210357330835)
  ·
    refine ⟨21623161794196815535996253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14415441196131210357330835 21623161794196815535996253)
    ·
      refine ⟨8108685672823805825998595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21623161794196815535996253 8108685672823805825998595)
      ·
        refine ⟨12163028509235708738997893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8108685672823805825998595 12163028509235708738997893)
        ·
          refine ⟨2280567845481695388562105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12163028509235708738997893 2280567845481695388562105)
          ·
            refine ⟨1710425884111271541421579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2280567845481695388562105 1710425884111271541421579)
            ·
              refine ⟨2565638826166907312132369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1710425884111271541421579 2565638826166907312132369)
              ·
                refine ⟨1924229119625180484099277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2565638826166907312132369 1924229119625180484099277)
                ·
                  refine ⟨721585919859442681537229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1924229119625180484099277 721585919859442681537229)
                  ·
                    refine ⟨270594719947291005576461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 721585919859442681537229 270594719947291005576461)
                    ·
                      rfl

theorem cell22_790472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 3, 3].length) (baseStart_790472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_790472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_790472 prefixEnd_790472 := by exact prefixLift 790472
  have htrace : WordTrace (prefixWord ++ tailWord_790472) baseStart_790472 baseEnd_790472 := by
    simpa [prefixWord, tailWord_790472, baseEnd_790472] using wordTrace_append hprefix tailTrace_790472
  have hstable : (prefixWord ++ tailWord_790472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790472).length < 2 ^ (prefixWord ++ tailWord_790472).sum := by decide
  have hdescent : baseEnd_790472 < baseStart_790472 := by decide
  rcases family_descends (prefixWord ++ tailWord_790472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790547 : List Nat := [1, 1, 1, 2, 1, 4, 5, 3, 4]
def baseStart_790547 : Nat := 118140960795 + 790547 * 2 ^ 59
def prefixEnd_790547 : Nat := 4983230072969 + 3 ^ 40 * 790547 * 2
def baseEnd_790547 : Nat := 90206797993338603317077

theorem tailTrace_790547 : CollatzResearch.WordTrace tailWord_790547 prefixEnd_790547 90206797993338603317077 := by
  unfold tailWord_790547
  simp only [CollatzResearch.WordTrace]
  refine ⟨28833617866990708523641895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19222411911327139015761263 28833617866990708523641895)
  ·
    refine ⟨43250426800486062785462843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28833617866990708523641895 43250426800486062785462843)
    ·
      refine ⟨64875640200729094178194265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43250426800486062785462843 64875640200729094178194265)
      ·
        refine ⟨48656730150546820633645699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64875640200729094178194265 48656730150546820633645699)
        ·
          refine ⟨72985095225820230950468549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48656730150546820633645699 72985095225820230950468549)
          ·
            refine ⟨13684705354841293303212853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72985095225820230950468549 13684705354841293303212853)
            ·
              refine ⟨1282941127016371247176205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13684705354841293303212853 1282941127016371247176205)
              ·
                refine ⟨481102922631139217691077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1282941127016371247176205 481102922631139217691077)
                ·
                  refine ⟨90206797993338603317077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 481102922631139217691077 90206797993338603317077)
                  ·
                    rfl

theorem cell22_790547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 3, 4].length) (baseStart_790547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_790547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_790547 prefixEnd_790547 := by exact prefixLift 790547
  have htrace : WordTrace (prefixWord ++ tailWord_790547) baseStart_790547 baseEnd_790547 := by
    simpa [prefixWord, tailWord_790547, baseEnd_790547] using wordTrace_append hprefix tailTrace_790547
  have hstable : (prefixWord ++ tailWord_790547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790547).length < 2 ^ (prefixWord ++ tailWord_790547).sum := by decide
  have hdescent : baseEnd_790547 < baseStart_790547 := by decide
  rcases family_descends (prefixWord ++ tailWord_790547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790562 : List Nat := [3, 3, 1, 1, 1, 2, 1, 3, 4, 3]
def baseStart_790562 : Nat := 118140960795 + 790562 * 2 ^ 59
def prefixEnd_790562 : Nat := 4983230072969 + 3 ^ 40 * 790562 * 2
def baseEnd_790562 : Nat := 270625528786560770826185

theorem tailTrace_790562 : CollatzResearch.WordTrace tailWord_790562 prefixEnd_790562 270625528786560770826185 := by
  unfold tailWord_790562
  simp only [CollatzResearch.WordTrace]
  refine ⟨7208541240484091521359485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19222776641290910723625293 7208541240484091521359485)
  ·
    refine ⟨2703202965181534320509807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7208541240484091521359485 2703202965181534320509807)
    ·
      refine ⟨4054804447772301480764711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2703202965181534320509807 4054804447772301480764711)
      ·
        refine ⟨6082206671658452221147067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4054804447772301480764711 6082206671658452221147067)
        ·
          refine ⟨9123310007487678331720601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6082206671658452221147067 9123310007487678331720601)
          ·
            refine ⟨6842482505615758748790451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9123310007487678331720601 6842482505615758748790451)
            ·
              refine ⟨10263723758423638123185677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6842482505615758748790451 10263723758423638123185677)
              ·
                refine ⟨3848896409408864296194629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10263723758423638123185677 3848896409408864296194629)
                ·
                  refine ⟨721668076764162055536493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3848896409408864296194629 721668076764162055536493)
                  ·
                    refine ⟨270625528786560770826185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 721668076764162055536493 270625528786560770826185)
                    ·
                      rfl

theorem cell22_790562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_790562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_790562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_790562 prefixEnd_790562 := by exact prefixLift 790562
  have htrace : WordTrace (prefixWord ++ tailWord_790562) baseStart_790562 baseEnd_790562 := by
    simpa [prefixWord, tailWord_790562, baseEnd_790562] using wordTrace_append hprefix tailTrace_790562
  have hstable : (prefixWord ++ tailWord_790562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790562).length < 2 ^ (prefixWord ++ tailWord_790562).sum := by decide
  have hdescent : baseEnd_790562 < baseStart_790562 := by decide
  rcases family_descends (prefixWord ++ tailWord_790562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790564 : List Nat := [2, 3, 1, 4, 2, 2, 1, 1, 6]
def baseStart_790564 : Nat := 118140960795 + 790564 * 2 ^ 59
def prefixEnd_790564 : Nat := 4983230072969 + 3 ^ 40 * 790564 * 2
def baseEnd_790564 : Nat := 90208737809144477425393

theorem tailTrace_790564 : CollatzResearch.WordTrace tailWord_790564 prefixEnd_790564 90208737809144477425393 := by
  unfold tailWord_790564
  simp only [CollatzResearch.WordTrace]
  refine ⟨14417118953964560213505373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19222825271952746951340497 14417118953964560213505373)
  ·
    refine ⟨5406419607736710080064515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14417118953964560213505373 5406419607736710080064515)
    ·
      refine ⟨8109629411605065120096773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5406419607736710080064515 8109629411605065120096773)
      ·
        refine ⟨1520555514675949710018145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8109629411605065120096773 1520555514675949710018145)
        ·
          refine ⟨1140416636006962282513609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1520555514675949710018145 1140416636006962282513609)
          ·
            refine ⟨855312477005221711885207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1140416636006962282513609 855312477005221711885207)
            ·
              refine ⟨1282968715507832567827811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 855312477005221711885207 1282968715507832567827811)
              ·
                refine ⟨1924453073261748851741717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1282968715507832567827811 1924453073261748851741717)
                ·
                  refine ⟨90208737809144477425393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1924453073261748851741717 90208737809144477425393)
                  ·
                    rfl

theorem cell22_790564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 6].length) (baseStart_790564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_790564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_790564 prefixEnd_790564 := by exact prefixLift 790564
  have htrace : WordTrace (prefixWord ++ tailWord_790564) baseStart_790564 baseEnd_790564 := by
    simpa [prefixWord, tailWord_790564, baseEnd_790564] using wordTrace_append hprefix tailTrace_790564
  have hstable : (prefixWord ++ tailWord_790564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790564).length < 2 ^ (prefixWord ++ tailWord_790564).sum := by decide
  have hdescent : baseEnd_790564 < baseStart_790564 := by decide
  rcases family_descends (prefixWord ++ tailWord_790564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790579 : List Nat := [1, 1, 1, 2, 4, 1, 6, 1, 2, 3]
def baseStart_790579 : Nat := 118140960795 + 790579 * 2 ^ 59
def prefixEnd_790579 : Nat := 4983230072969 + 3 ^ 40 * 790579 * 2
def baseEnd_790579 : Nat := 270631348233978393151133

theorem tailTrace_790579 : CollatzResearch.WordTrace tailWord_790579 prefixEnd_790579 270631348233978393151133 := by
  unfold tailWord_790579
  simp only [CollatzResearch.WordTrace]
  refine ⟨28834785002874777988806791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19223190001916518659204527 28834785002874777988806791)
  ·
    refine ⟨43252177504312166983210187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28834785002874777988806791 43252177504312166983210187)
    ·
      refine ⟨64878266256468250474815281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43252177504312166983210187 64878266256468250474815281)
      ·
        refine ⟨48658699692351187856111461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64878266256468250474815281 48658699692351187856111461)
        ·
          refine ⟨9123506192315847723020899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48658699692351187856111461 9123506192315847723020899)
          ·
            refine ⟨13685259288473771584531349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9123506192315847723020899 13685259288473771584531349)
            ·
              refine ⟨641496529147208043024907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13685259288473771584531349 641496529147208043024907)
              ·
                refine ⟨962244793720812064537361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 641496529147208043024907 962244793720812064537361)
                ·
                  refine ⟨721683595290609048403021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 962244793720812064537361 721683595290609048403021)
                  ·
                    refine ⟨270631348233978393151133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 721683595290609048403021 270631348233978393151133)
                    ·
                      rfl

theorem cell22_790579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 1, 2, 3].length) (baseStart_790579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_790579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_790579 prefixEnd_790579 := by exact prefixLift 790579
  have htrace : WordTrace (prefixWord ++ tailWord_790579) baseStart_790579 baseEnd_790579 := by
    simpa [prefixWord, tailWord_790579, baseEnd_790579] using wordTrace_append hprefix tailTrace_790579
  have hstable : (prefixWord ++ tailWord_790579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790579).length < 2 ^ (prefixWord ++ tailWord_790579).sum := by decide
  have hdescent : baseEnd_790579 < baseStart_790579 := by decide
  rcases family_descends (prefixWord ++ tailWord_790579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
