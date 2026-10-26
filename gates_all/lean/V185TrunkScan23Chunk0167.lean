import V185TrunkScan23Chunk0166

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_987448 : List Nat := [2, 1, 2, 1, 3, 1, 2, 2, 1, 3, 5]
def baseStart_987448 : Nat := 118140960795 + 987448 * 2 ^ 59
def prefixEnd_987448 : Nat := 4983230072969 + 3 ^ 40 * 987448 * 2
def baseEnd_987448 : Nat := 507035445320957838858815

theorem tailTrace_987448 : CollatzResearch.WordTrace tailWord_987448 prefixEnd_987448 507035445320957838858815 := by
  unfold tailWord_987448
  simp only [CollatzResearch.WordTrace]
  refine ⟨18007593663326006768589499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24010124884434675691452665 18007593663326006768589499)
  ·
    refine ⟨27011390494989010152884249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18007593663326006768589499 27011390494989010152884249)
    ·
      refine ⟨20258542871241757614663187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27011390494989010152884249 20258542871241757614663187)
      ·
        refine ⟨30387814306862636421994781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20258542871241757614663187 30387814306862636421994781)
        ·
          refine ⟨11395430365073488658248043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30387814306862636421994781 11395430365073488658248043)
          ·
            refine ⟨17093145547610232987372065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11395430365073488658248043 17093145547610232987372065)
            ·
              refine ⟨12819859160707674740529049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17093145547610232987372065 12819859160707674740529049)
              ·
                refine ⟨9614894370530756055396787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12819859160707674740529049 9614894370530756055396787)
                ·
                  refine ⟨14422341555796134083095181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9614894370530756055396787 14422341555796134083095181)
                  ·
                    refine ⟨5408378083423550281160693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14422341555796134083095181 5408378083423550281160693)
                    ·
                      refine ⟨507035445320957838858815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5408378083423550281160693 507035445320957838858815)
                      ·
                        rfl

theorem cell23_987448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 1, 3, 5].length) (baseStart_987448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_987448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_987448 prefixEnd_987448 := by exact prefixLift 987448
  have htrace : WordTrace (prefixWord ++ tailWord_987448) baseStart_987448 baseEnd_987448 := by
    simpa [prefixWord, tailWord_987448, baseEnd_987448] using wordTrace_append hprefix tailTrace_987448
  have hstable : (prefixWord ++ tailWord_987448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987448).length < 2 ^ (prefixWord ++ tailWord_987448).sum := by decide
  have hdescent : baseEnd_987448 < baseStart_987448 := by decide
  rcases family_descends (prefixWord ++ tailWord_987448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987496 : List Nat := [2, 1, 4, 2, 2, 1, 3, 2, 2, 2, 2]
def baseStart_987496 : Nat := 118140960795 + 987496 * 2 ^ 59
def prefixEnd_987496 : Nat := 4983230072969 + 3 ^ 40 * 987496 * 2
def baseEnd_987496 : Nat := 507060092392373651058595

theorem tailTrace_987496 : CollatzResearch.WordTrace tailWord_987496 prefixEnd_987496 507060092392373651058595 := by
  unfold tailWord_987496
  simp only [CollatzResearch.WordTrace]
  refine ⟨18008469015239058867463171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24011292020318745156617561 18008469015239058867463171)
  ·
    refine ⟨27012703522858588301194757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18008469015239058867463171 27012703522858588301194757)
    ·
      refine ⟨5064881910535985306474017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27012703522858588301194757 5064881910535985306474017)
      ·
        refine ⟨3798661432901988979855513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5064881910535985306474017 3798661432901988979855513)
        ·
          refine ⟨2848996074676491734891635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3798661432901988979855513 2848996074676491734891635)
          ·
            refine ⟨4273494112014737602337453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2848996074676491734891635 4273494112014737602337453)
            ·
              refine ⟨1602560292005526600876545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4273494112014737602337453 1602560292005526600876545)
              ·
                refine ⟨1201920219004144950657409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1602560292005526600876545 1201920219004144950657409)
                ·
                  refine ⟨901440164253108712993057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1201920219004144950657409 901440164253108712993057)
                  ·
                    refine ⟨676080123189831534744793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 901440164253108712993057 676080123189831534744793)
                    ·
                      refine ⟨507060092392373651058595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 676080123189831534744793 507060092392373651058595)
                      ·
                        rfl

theorem cell23_987496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_987496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_987496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_987496 prefixEnd_987496 := by exact prefixLift 987496
  have htrace : WordTrace (prefixWord ++ tailWord_987496) baseStart_987496 baseEnd_987496 := by
    simpa [prefixWord, tailWord_987496, baseEnd_987496] using wordTrace_append hprefix tailTrace_987496
  have hstable : (prefixWord ++ tailWord_987496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987496).length < 2 ^ (prefixWord ++ tailWord_987496).sum := by decide
  have hdescent : baseEnd_987496 < baseStart_987496 := by decide
  rcases family_descends (prefixWord ++ tailWord_987496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987552 : List Nat := [2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 4]
def baseStart_987552 : Nat := 118140960795 + 987552 * 2 ^ 59
def prefixEnd_987552 : Nat := 4983230072969 + 3 ^ 40 * 987552 * 2
def baseEnd_987552 : Nat := 507088847309025431958337

theorem tailTrace_987552 : CollatzResearch.WordTrace tailWord_987552 prefixEnd_987552 507088847309025431958337 := by
  unfold tailWord_987552
  simp only [CollatzResearch.WordTrace]
  refine ⟨18009490259137619649482455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24012653678850159532643273 18009490259137619649482455)
  ·
    refine ⟨27014235388706429474223683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18009490259137619649482455 27014235388706429474223683)
    ·
      refine ⟨40521353083059644211335525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27014235388706429474223683 40521353083059644211335525)
      ·
        refine ⟨7597753703073683289625411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40521353083059644211335525 7597753703073683289625411)
        ·
          refine ⟨11396630554610524934438117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7597753703073683289625411 11396630554610524934438117)
          ·
            refine ⟨2136868228989473425207147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11396630554610524934438117 2136868228989473425207147)
            ·
              refine ⟨3205302343484210137810721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2136868228989473425207147 3205302343484210137810721)
              ·
                refine ⟨2403976757613157603358041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3205302343484210137810721 2403976757613157603358041)
                ·
                  refine ⟨1802982568209868202518531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2403976757613157603358041 1802982568209868202518531)
                  ·
                    refine ⟨2704473852314802303777797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1802982568209868202518531 2704473852314802303777797)
                    ·
                      refine ⟨507088847309025431958337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2704473852314802303777797 507088847309025431958337)
                      ·
                        rfl

theorem cell23_987552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_987552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_987552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_987552 prefixEnd_987552 := by exact prefixLift 987552
  have htrace : WordTrace (prefixWord ++ tailWord_987552) baseStart_987552 baseEnd_987552 := by
    simpa [prefixWord, tailWord_987552, baseEnd_987552] using wordTrace_append hprefix tailTrace_987552
  have hstable : (prefixWord ++ tailWord_987552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987552).length < 2 ^ (prefixWord ++ tailWord_987552).sum := by decide
  have hdescent : baseEnd_987552 < baseStart_987552 := by decide
  rcases family_descends (prefixWord ++ tailWord_987552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987642 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 1, 8, 2]
def baseStart_987642 : Nat := 118140960795 + 987642 * 2 ^ 59
def prefixEnd_987642 : Nat := 4983230072969 + 3 ^ 40 * 987642 * 2
def baseEnd_987642 : Nat := 507135060567930079832923

theorem tailTrace_987642 : CollatzResearch.WordTrace tailWord_987642 prefixEnd_987642 507135060567930079832923 := by
  unfold tailWord_987642
  simp only [CollatzResearch.WordTrace]
  refine ⟨9005565771987296167435295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24014842058632789779827453 9005565771987296167435295)
  ·
    refine ⟨13508348657980944251152943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9005565771987296167435295 13508348657980944251152943)
    ·
      refine ⟨20262522986971416376729415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13508348657980944251152943 20262522986971416376729415)
      ·
        refine ⟨30393784480457124565094123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20262522986971416376729415 30393784480457124565094123)
        ·
          refine ⟨45590676720685686847641185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30393784480457124565094123 45590676720685686847641185)
          ·
            refine ⟨34193007540514265135730889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45590676720685686847641185 34193007540514265135730889)
            ·
              refine ⟨25644755655385698851798167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34193007540514265135730889 25644755655385698851798167)
              ·
                refine ⟨38467133483078548277697251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25644755655385698851798167 38467133483078548277697251)
                ·
                  refine ⟨57700700224617822416545877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38467133483078548277697251 57700700224617822416545877)
                  ·
                    refine ⟨676180080757240106443897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 57700700224617822416545877 676180080757240106443897)
                    ·
                      refine ⟨507135060567930079832923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 676180080757240106443897 507135060567930079832923)
                      ·
                        rfl

theorem cell23_987642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 1, 8, 2].length) (baseStart_987642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_987642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_987642 prefixEnd_987642 := by exact prefixLift 987642
  have htrace : WordTrace (prefixWord ++ tailWord_987642) baseStart_987642 baseEnd_987642 := by
    simpa [prefixWord, tailWord_987642, baseEnd_987642] using wordTrace_append hprefix tailTrace_987642
  have hstable : (prefixWord ++ tailWord_987642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987642).length < 2 ^ (prefixWord ++ tailWord_987642).sum := by decide
  have hdescent : baseEnd_987642 < baseStart_987642 := by decide
  rcases family_descends (prefixWord ++ tailWord_987642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987659 : List Nat := [1, 1, 1, 1, 7, 2, 1, 3, 1, 1, 4]
def baseStart_987659 : Nat := 118140960795 + 987659 * 2 ^ 59
def prefixEnd_987659 : Nat := 4983230072969 + 3 ^ 40 * 987659 * 2
def baseEnd_987659 : Nat := 507143789739056513320345

theorem tailTrace_987659 : CollatzResearch.WordTrace tailWord_987659 prefixEnd_987659 507143789739056513320345 := by
  unfold tailWord_987659
  simp only [CollatzResearch.WordTrace]
  refine ⟨36022883128887596573110031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24015255419258397715406687 36022883128887596573110031)
  ·
    refine ⟨54034324693331394859665047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36022883128887596573110031 54034324693331394859665047)
    ·
      refine ⟨81051487039997092289497571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54034324693331394859665047 81051487039997092289497571)
      ·
        refine ⟨121577230559995638434246357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81051487039997092289497571 121577230559995638434246357)
        ·
          refine ⟨2849466341249897775802649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 121577230559995638434246357 2849466341249897775802649)
          ·
            refine ⟨2137099755937423331851987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2849466341249897775802649 2137099755937423331851987)
            ·
              refine ⟨3205649633906134997777981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2137099755937423331851987 3205649633906134997777981)
              ·
                refine ⟨1202118612714800624166743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3205649633906134997777981 1202118612714800624166743)
                ·
                  refine ⟨1803177919072200936250115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1202118612714800624166743 1803177919072200936250115)
                  ·
                    refine ⟨2704766878608301404375173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1803177919072200936250115 2704766878608301404375173)
                    ·
                      refine ⟨507143789739056513320345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2704766878608301404375173 507143789739056513320345)
                      ·
                        rfl

theorem cell23_987659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 3, 1, 1, 4].length) (baseStart_987659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_987659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_987659 prefixEnd_987659 := by exact prefixLift 987659
  have htrace : WordTrace (prefixWord ++ tailWord_987659) baseStart_987659 baseEnd_987659 := by
    simpa [prefixWord, tailWord_987659, baseEnd_987659] using wordTrace_append hprefix tailTrace_987659
  have hstable : (prefixWord ++ tailWord_987659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987659).length < 2 ^ (prefixWord ++ tailWord_987659).sum := by decide
  have hdescent : baseEnd_987659 < baseStart_987659 := by decide
  rcases family_descends (prefixWord ++ tailWord_987659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987676 : List Nat := [2, 2, 3, 1, 2, 2, 1, 3, 3, 2, 2]
def baseStart_987676 : Nat := 118140960795 + 987676 * 2 ^ 59
def prefixEnd_987676 : Nat := 4983230072969 + 3 ^ 40 * 987676 * 2
def baseEnd_987676 : Nat := 507152518910182946807767

theorem tailTrace_987676 : CollatzResearch.WordTrace tailWord_987676 prefixEnd_987676 507152518910182946807767 := by
  unfold tailWord_987676
  simp only [CollatzResearch.WordTrace]
  refine ⟨18011751584913004238239441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24015668779884005650985921 18011751584913004238239441)
  ·
    refine ⟨13508813688684753178679581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18011751584913004238239441 13508813688684753178679581)
    ·
      refine ⟨5065805133256782442004843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13508813688684753178679581 5065805133256782442004843)
      ·
        refine ⟨7598707699885173663007265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5065805133256782442004843 7598707699885173663007265)
        ·
          refine ⟨5699030774913880247255449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7598707699885173663007265 5699030774913880247255449)
          ·
            refine ⟨4274273081185410185441587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5699030774913880247255449 4274273081185410185441587)
            ·
              refine ⟨6411409621778115278162381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4274273081185410185441587 6411409621778115278162381)
              ·
                refine ⟨2404278608166793229310893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6411409621778115278162381 2404278608166793229310893)
                ·
                  refine ⟨901604478062547460991585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2404278608166793229310893 901604478062547460991585)
                  ·
                    refine ⟨676203358546910595743689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 901604478062547460991585 676203358546910595743689)
                    ·
                      refine ⟨507152518910182946807767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 676203358546910595743689 507152518910182946807767)
                      ·
                        rfl

theorem cell23_987676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 3, 2, 2].length) (baseStart_987676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_987676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_987676 prefixEnd_987676 := by exact prefixLift 987676
  have htrace : WordTrace (prefixWord ++ tailWord_987676) baseStart_987676 baseEnd_987676 := by
    simpa [prefixWord, tailWord_987676, baseEnd_987676] using wordTrace_append hprefix tailTrace_987676
  have hstable : (prefixWord ++ tailWord_987676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987676).length < 2 ^ (prefixWord ++ tailWord_987676).sum := by decide
  have hdescent : baseEnd_987676 < baseStart_987676 := by decide
  rcases family_descends (prefixWord ++ tailWord_987676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987715 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 8]
def baseStart_987715 : Nat := 118140960795 + 987715 * 2 ^ 59
def prefixEnd_987715 : Nat := 4983230072969 + 3 ^ 40 * 987715 * 2
def baseEnd_987715 : Nat := 507172544655708294220087

theorem tailTrace_987715 : CollatzResearch.WordTrace tailWord_987715 prefixEnd_987715 507172544655708294220087 := by
  unfold tailWord_987715
  simp only [CollatzResearch.WordTrace]
  refine ⟨36024925616684718137148599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24016617077789812091432399 36024925616684718137148599)
  ·
    refine ⟨54037388425027077205722899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36024925616684718137148599 54037388425027077205722899)
    ·
      refine ⟨81056082637540615808584349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54037388425027077205722899 81056082637540615808584349)
      ·
        refine ⟨30396030989077730928219131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81056082637540615808584349 30396030989077730928219131)
        ·
          refine ⟨45594046483616596392328697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30396030989077730928219131 45594046483616596392328697)
          ·
            refine ⟨34195534862712447294246523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45594046483616596392328697 34195534862712447294246523)
            ·
              refine ⟨51293302294068670941369785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34195534862712447294246523 51293302294068670941369785)
              ·
                refine ⟨38469976720551503206027339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51293302294068670941369785 38469976720551503206027339)
                ·
                  refine ⟨57704965080827254809041009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38469976720551503206027339 57704965080827254809041009)
                  ·
                    refine ⟨43278723810620441106780757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57704965080827254809041009 43278723810620441106780757)
                    ·
                      refine ⟨507172544655708294220087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 43278723810620441106780757 507172544655708294220087)
                      ·
                        rfl

theorem cell23_987715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 8].length) (baseStart_987715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_987715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_987715 prefixEnd_987715 := by exact prefixLift 987715
  have htrace : WordTrace (prefixWord ++ tailWord_987715) baseStart_987715 baseEnd_987715 := by
    simpa [prefixWord, tailWord_987715, baseEnd_987715] using wordTrace_append hprefix tailTrace_987715
  have hstable : (prefixWord ++ tailWord_987715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987715).length < 2 ^ (prefixWord ++ tailWord_987715).sum := by decide
  have hdescent : baseEnd_987715 < baseStart_987715 := by decide
  rcases family_descends (prefixWord ++ tailWord_987715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987778 : List Nat := [3, 4, 3, 1, 1, 2, 2, 2, 1, 2, 2]
def baseStart_987778 : Nat := 118140960795 + 987778 * 2 ^ 59
def prefixEnd_987778 : Nat := 4983230072969 + 3 ^ 40 * 987778 * 2
def baseEnd_987778 : Nat := 507204893936941547732299

theorem tailTrace_987778 : CollatzResearch.WordTrace tailWord_987778 prefixEnd_987778 507204893936941547732299 := by
  unfold tailWord_987778
  simp only [CollatzResearch.WordTrace]
  refine ⟨9006805853864119974172997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24018148943637653264461325 9006805853864119974172997)
  ·
    refine ⟨1688776097599522495157437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9006805853864119974172997 1688776097599522495157437)
    ·
      refine ⟨633291036599820935684039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1688776097599522495157437 633291036599820935684039)
      ·
        refine ⟨949936554899731403526059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 633291036599820935684039 949936554899731403526059)
        ·
          refine ⟨1424904832349597105289089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 949936554899731403526059 1424904832349597105289089)
          ·
            refine ⟨1068678624262197828966817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1424904832349597105289089 1068678624262197828966817)
            ·
              refine ⟨801508968196648371725113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1068678624262197828966817 801508968196648371725113)
              ·
                refine ⟨601131726147486278793835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 801508968196648371725113 601131726147486278793835)
                ·
                  refine ⟨901697589221229418190753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 601131726147486278793835 901697589221229418190753)
                  ·
                    refine ⟨676273191915922063643065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 901697589221229418190753 676273191915922063643065)
                    ·
                      refine ⟨507204893936941547732299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 676273191915922063643065 507204893936941547732299)
                      ·
                        rfl

theorem cell23_987778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_987778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_987778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_987778 prefixEnd_987778 := by exact prefixLift 987778
  have htrace : WordTrace (prefixWord ++ tailWord_987778) baseStart_987778 baseEnd_987778 := by
    simpa [prefixWord, tailWord_987778, baseEnd_987778] using wordTrace_append hprefix tailTrace_987778
  have hstable : (prefixWord ++ tailWord_987778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987778).length < 2 ^ (prefixWord ++ tailWord_987778).sum := by decide
  have hdescent : baseEnd_987778 < baseStart_987778 := by decide
  rcases family_descends (prefixWord ++ tailWord_987778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987783 : List Nat := [1, 1, 4, 2, 1, 2, 4, 2, 2, 2, 2]
def baseStart_987783 : Nat := 118140960795 + 987783 * 2 ^ 59
def prefixEnd_987783 : Nat := 4983230072969 + 3 ^ 40 * 987783 * 2
def baseEnd_987783 : Nat := 507207461340214028169775

theorem tailTrace_987783 : CollatzResearch.WordTrace tailWord_987783 prefixEnd_987783 507207461340214028169775 := by
  unfold tailWord_987783
  simp only [CollatzResearch.WordTrace]
  refine ⟨36027405780438365750624003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24018270520292243833749335 36027405780438365750624003)
  ·
    refine ⟨54041108670657548625936005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36027405780438365750624003 54041108670657548625936005)
    ·
      refine ⟨10132707875748290367363001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54041108670657548625936005 10132707875748290367363001)
      ·
        refine ⟨7599530906811217775522251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10132707875748290367363001 7599530906811217775522251)
        ·
          refine ⟨11399296360216826663283377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7599530906811217775522251 11399296360216826663283377)
          ·
            refine ⟨8549472270162619997462533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11399296360216826663283377 8549472270162619997462533)
            ·
              refine ⟨1603026050655491249524225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8549472270162619997462533 1603026050655491249524225)
              ·
                refine ⟨1202269537991618437143169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1603026050655491249524225 1202269537991618437143169)
                ·
                  refine ⟨901702153493713827857377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1202269537991618437143169 901702153493713827857377)
                  ·
                    refine ⟨676276615120285370893033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 901702153493713827857377 676276615120285370893033)
                    ·
                      refine ⟨507207461340214028169775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 676276615120285370893033 507207461340214028169775)
                      ·
                        rfl

theorem cell23_987783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 2, 2, 2, 2].length) (baseStart_987783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_987783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_987783 prefixEnd_987783 := by exact prefixLift 987783
  have htrace : WordTrace (prefixWord ++ tailWord_987783) baseStart_987783 baseEnd_987783 := by
    simpa [prefixWord, tailWord_987783, baseEnd_987783] using wordTrace_append hprefix tailTrace_987783
  have hstable : (prefixWord ++ tailWord_987783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987783).length < 2 ^ (prefixWord ++ tailWord_987783).sum := by decide
  have hdescent : baseEnd_987783 < baseStart_987783 := by decide
  rcases family_descends (prefixWord ++ tailWord_987783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987796 : List Nat := [2, 4, 2, 2, 1, 2, 1, 1, 2, 2, 4]
def baseStart_987796 : Nat := 118140960795 + 987796 * 2 ^ 59
def prefixEnd_987796 : Nat := 4983230072969 + 3 ^ 40 * 987796 * 2
def baseEnd_987796 : Nat := 507214136588722477307215

theorem tailTrace_987796 : CollatzResearch.WordTrace tailWord_987796 prefixEnd_987796 507214136588722477307215 := by
  unfold tailWord_987796
  simp only [CollatzResearch.WordTrace]
  refine ⟨18013939964695634485423621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24018586619594179313898161 18013939964695634485423621)
  ·
    refine ⟨3377613743380431466016929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18013939964695634485423621 3377613743380431466016929)
    ·
      refine ⟨2533210307535323599512697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3377613743380431466016929 2533210307535323599512697)
      ·
        refine ⟨1899907730651492699634523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2533210307535323599512697 1899907730651492699634523)
        ·
          refine ⟨2849861595977239049451785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1899907730651492699634523 2849861595977239049451785)
          ·
            refine ⟨2137396196982929287088839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2849861595977239049451785 2137396196982929287088839)
            ·
              refine ⟨3206094295474393930633259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2137396196982929287088839 3206094295474393930633259)
              ·
                refine ⟨4809141443211590895949889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3206094295474393930633259 4809141443211590895949889)
                ·
                  refine ⟨3606856082408693171962417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4809141443211590895949889 3606856082408693171962417)
                  ·
                    refine ⟨2705142061806519878971813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3606856082408693171962417 2705142061806519878971813)
                    ·
                      refine ⟨507214136588722477307215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2705142061806519878971813 507214136588722477307215)
                      ·
                        rfl

theorem cell23_987796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_987796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_987796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_987796 prefixEnd_987796 := by exact prefixLift 987796
  have htrace : WordTrace (prefixWord ++ tailWord_987796) baseStart_987796 baseEnd_987796 := by
    simpa [prefixWord, tailWord_987796, baseEnd_987796] using wordTrace_append hprefix tailTrace_987796
  have hstable : (prefixWord ++ tailWord_987796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987796).length < 2 ^ (prefixWord ++ tailWord_987796).sum := by decide
  have hdescent : baseEnd_987796 < baseStart_987796 := by decide
  rcases family_descends (prefixWord ++ tailWord_987796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987799 : List Nat := [1, 1, 3, 3, 2, 1, 3, 1, 2, 3, 3]
def baseStart_987799 : Nat := 118140960795 + 987799 * 2 ^ 59
def prefixEnd_987799 : Nat := 4983230072969 + 3 ^ 40 * 987799 * 2
def baseEnd_987799 : Nat := 507215677030685965569701

theorem tailTrace_987799 : CollatzResearch.WordTrace tailWord_987799 prefixEnd_987799 507215677030685965569701 := by
  unfold tailWord_987799
  simp only [CollatzResearch.WordTrace]
  refine ⟨36027989348380400483206451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24018659565586933655470967 36027989348380400483206451)
  ·
    refine ⟨54041984022570600724809677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36027989348380400483206451 54041984022570600724809677)
    ·
      refine ⟨20265744008463975271803629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54041984022570600724809677 20265744008463975271803629)
      ·
        refine ⟨7599654003173990726926361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20265744008463975271803629 7599654003173990726926361)
        ·
          refine ⟨5699740502380493045194771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7599654003173990726926361 5699740502380493045194771)
          ·
            refine ⟨8549610753570739567792157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5699740502380493045194771 8549610753570739567792157)
            ·
              refine ⟨3206104032589027337922059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8549610753570739567792157 3206104032589027337922059)
              ·
                refine ⟨4809156048883541006883089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3206104032589027337922059 4809156048883541006883089)
                ·
                  refine ⟨3606867036662655755162317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4809156048883541006883089 3606867036662655755162317)
                  ·
                    refine ⟨1352575138748495908185869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3606867036662655755162317 1352575138748495908185869)
                    ·
                      refine ⟨507215677030685965569701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1352575138748495908185869 507215677030685965569701)
                      ·
                        rfl

theorem cell23_987799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_987799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_987799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_987799 prefixEnd_987799 := by exact prefixLift 987799
  have htrace : WordTrace (prefixWord ++ tailWord_987799) baseStart_987799 baseEnd_987799 := by
    simpa [prefixWord, tailWord_987799, baseEnd_987799] using wordTrace_append hprefix tailTrace_987799
  have hstable : (prefixWord ++ tailWord_987799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987799).length < 2 ^ (prefixWord ++ tailWord_987799).sum := by decide
  have hdescent : baseEnd_987799 < baseStart_987799 := by decide
  rcases family_descends (prefixWord ++ tailWord_987799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987900 : List Nat := [2, 2, 2, 1, 3, 3, 3, 2, 1, 4]
def baseStart_987900 : Nat := 118140960795 + 987900 * 2 ^ 59
def prefixEnd_987900 : Nat := 4983230072969 + 3 ^ 40 * 987900 * 2
def baseEnd_987900 : Nat := 169089179525596690135579

theorem tailTrace_987900 : CollatzResearch.WordTrace tailWord_987900 prefixEnd_987900 169089179525596690135579 := by
  unfold tailWord_987900
  simp only [CollatzResearch.WordTrace]
  refine ⟨18015836560507247366316577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24021115414009663155088769 18015836560507247366316577)
  ·
    refine ⟨13511877420380435524737433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18015836560507247366316577 13511877420380435524737433)
    ·
      refine ⟨10133908065285326643553075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13511877420380435524737433 10133908065285326643553075)
      ·
        refine ⟨15200862097927989965329613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10133908065285326643553075 15200862097927989965329613)
        ·
          refine ⟨5700323286722996236998605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15200862097927989965329613 5700323286722996236998605)
          ·
            refine ⟨2137621232521123588874477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5700323286722996236998605 2137621232521123588874477)
            ·
              refine ⟨801607962195421345827929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2137621232521123588874477 801607962195421345827929)
              ·
                refine ⟨601205971646566009370947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 801607962195421345827929 601205971646566009370947)
                ·
                  refine ⟨901808957469849014056421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 601205971646566009370947 901808957469849014056421)
                  ·
                    refine ⟨169089179525596690135579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 901808957469849014056421 169089179525596690135579)
                    ·
                      rfl

theorem cell23_987900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 2, 1, 4].length) (baseStart_987900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_987900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_987900 prefixEnd_987900 := by exact prefixLift 987900
  have htrace : WordTrace (prefixWord ++ tailWord_987900) baseStart_987900 baseEnd_987900 := by
    simpa [prefixWord, tailWord_987900, baseEnd_987900] using wordTrace_append hprefix tailTrace_987900
  have hstable : (prefixWord ++ tailWord_987900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987900).length < 2 ^ (prefixWord ++ tailWord_987900).sum := by decide
  have hdescent : baseEnd_987900 < baseStart_987900 := by decide
  rcases family_descends (prefixWord ++ tailWord_987900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987916 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 6, 3, 2]
def baseStart_987916 : Nat := 118140960795 + 987916 * 2 ^ 59
def prefixEnd_987916 : Nat := 4983230072969 + 3 ^ 40 * 987916 * 2
def baseEnd_987916 : Nat := 507275754267262007806663

theorem tailTrace_987916 : CollatzResearch.WordTrace tailWord_987916 prefixEnd_987916 507275754267262007806663 := by
  unfold tailWord_987916
  simp only [CollatzResearch.WordTrace]
  refine ⟨18016128344478264732607801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24021504459304352976810401 18016128344478264732607801)
  ·
    refine ⟨13512096258358698549455851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18016128344478264732607801 13512096258358698549455851)
    ·
      refine ⟨20268144387538047824183777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13512096258358698549455851 20268144387538047824183777)
      ·
        refine ⟨15201108290653535868137833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20268144387538047824183777 15201108290653535868137833)
        ·
          refine ⟨11400831217990151901103375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15201108290653535868137833 11400831217990151901103375)
          ·
            refine ⟨17101246826985227851655063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11400831217990151901103375 17101246826985227851655063)
            ·
              refine ⟨25651870240477841777482595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17101246826985227851655063 25651870240477841777482595)
              ·
                refine ⟨38477805360716762666223893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25651870240477841777482595 38477805360716762666223893)
                ·
                  refine ⟨1803647126283598249979245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 38477805360716762666223893 1803647126283598249979245)
                  ·
                    refine ⟨676367672356349343742217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1803647126283598249979245 676367672356349343742217)
                    ·
                      refine ⟨507275754267262007806663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 676367672356349343742217 507275754267262007806663)
                      ·
                        rfl

theorem cell23_987916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 6, 3, 2].length) (baseStart_987916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_987916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_987916 prefixEnd_987916 := by exact prefixLift 987916
  have htrace : WordTrace (prefixWord ++ tailWord_987916) baseStart_987916 baseEnd_987916 := by
    simpa [prefixWord, tailWord_987916, baseEnd_987916] using wordTrace_append hprefix tailTrace_987916
  have hstable : (prefixWord ++ tailWord_987916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987916).length < 2 ^ (prefixWord ++ tailWord_987916).sum := by decide
  have hdescent : baseEnd_987916 < baseStart_987916 := by decide
  rcases family_descends (prefixWord ++ tailWord_987916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987950 : List Nat := [4, 1, 3, 2, 1, 1, 2, 2, 2, 3, 2]
def baseStart_987950 : Nat := 118140960795 + 987950 * 2 ^ 59
def prefixEnd_987950 : Nat := 4983230072969 + 3 ^ 40 * 987950 * 2
def baseEnd_987950 : Nat := 507293212609514874781507

theorem tailTrace_987950 : CollatzResearch.WordTrace tailWord_987950 prefixEnd_987950 507293212609514874781507 := by
  unfold tailWord_987950
  simp only [CollatzResearch.WordTrace]
  refine ⟨4504187096354169158994163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24022331180555568847968869 4504187096354169158994163)
  ·
    refine ⟨6756280644531253738491245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4504187096354169158994163 6756280644531253738491245)
    ·
      refine ⟨2533605241699220151934217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6756280644531253738491245 2533605241699220151934217)
      ·
        refine ⟨1900203931274415113950663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2533605241699220151934217 1900203931274415113950663)
        ·
          refine ⟨2850305896911622670925995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1900203931274415113950663 2850305896911622670925995)
          ·
            refine ⟨4275458845367434006388993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2850305896911622670925995 4275458845367434006388993)
            ·
              refine ⟨3206594134025575504791745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4275458845367434006388993 3206594134025575504791745)
              ·
                refine ⟨2404945600519181628593809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3206594134025575504791745 2404945600519181628593809)
                ·
                  refine ⟨1803709200389386221445357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2404945600519181628593809 1803709200389386221445357)
                  ·
                    refine ⟨676390950146019833042009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1803709200389386221445357 676390950146019833042009)
                    ·
                      refine ⟨507293212609514874781507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 676390950146019833042009 507293212609514874781507)
                      ·
                        rfl

theorem cell23_987950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_987950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_987950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_987950 prefixEnd_987950 := by exact prefixLift 987950
  have htrace : WordTrace (prefixWord ++ tailWord_987950) baseStart_987950 baseEnd_987950 := by
    simpa [prefixWord, tailWord_987950, baseEnd_987950] using wordTrace_append hprefix tailTrace_987950
  have hstable : (prefixWord ++ tailWord_987950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987950).length < 2 ^ (prefixWord ++ tailWord_987950).sum := by decide
  have hdescent : baseEnd_987950 < baseStart_987950 := by decide
  rcases family_descends (prefixWord ++ tailWord_987950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987957 : List Nat := [1, 3, 3, 1, 3, 1, 4, 2, 1, 1, 3]
def baseStart_987957 : Nat := 118140960795 + 987957 * 2 ^ 59
def prefixEnd_987957 : Nat := 4983230072969 + 3 ^ 40 * 987957 * 2
def baseEnd_987957 : Nat := 507296806974096347393975

theorem tailTrace_987957 : CollatzResearch.WordTrace tailWord_987957 prefixEnd_987957 507296806974096347393975 := by
  unfold tailWord_987957
  simp only [CollatzResearch.WordTrace]
  refine ⟨36033752081807993467458125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24022501387871995644972083 36033752081807993467458125)
  ·
    refine ⟨13512657030677997550296797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36033752081807993467458125 13512657030677997550296797)
    ·
      refine ⟨5067246386504249081361299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13512657030677997550296797 5067246386504249081361299)
      ·
        refine ⟨7600869579756373622041949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5067246386504249081361299 7600869579756373622041949)
        ·
          refine ⟨2850326092408640108265731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7600869579756373622041949 2850326092408640108265731)
          ·
            refine ⟨4275489138612960162398597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2850326092408640108265731 4275489138612960162398597)
            ·
              refine ⟨801654213489930030449737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4275489138612960162398597 801654213489930030449737)
              ·
                refine ⟨601240660117447522837303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 801654213489930030449737 601240660117447522837303)
                ·
                  refine ⟨901860990176171284255955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 601240660117447522837303 901860990176171284255955)
                  ·
                    refine ⟨1352791485264256926383933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 901860990176171284255955 1352791485264256926383933)
                    ·
                      refine ⟨507296806974096347393975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1352791485264256926383933 507296806974096347393975)
                      ·
                        rfl

theorem cell23_987957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 2, 1, 1, 3].length) (baseStart_987957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_987957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_987957 prefixEnd_987957 := by exact prefixLift 987957
  have htrace : WordTrace (prefixWord ++ tailWord_987957) baseStart_987957 baseEnd_987957 := by
    simpa [prefixWord, tailWord_987957, baseEnd_987957] using wordTrace_append hprefix tailTrace_987957
  have hstable : (prefixWord ++ tailWord_987957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987957).length < 2 ^ (prefixWord ++ tailWord_987957).sum := by decide
  have hdescent : baseEnd_987957 < baseStart_987957 := by decide
  rcases family_descends (prefixWord ++ tailWord_987957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987959 : List Nat := [1, 1, 3, 1, 2, 1, 3, 2, 3, 2, 4]
def baseStart_987959 : Nat := 118140960795 + 987959 * 2 ^ 59
def prefixEnd_987959 : Nat := 4983230072969 + 3 ^ 40 * 987959 * 2
def baseEnd_987959 : Nat := 507297833935405339568965

theorem tailTrace_987959 : CollatzResearch.WordTrace tailWord_987959 prefixEnd_987959 507297833935405339568965 := by
  unfold tailWord_987959
  simp only [CollatzResearch.WordTrace]
  refine ⟨36033825027800747809030931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24022550018533831872687287 36033825027800747809030931)
  ·
    refine ⟨54050737541701121713546397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36033825027800747809030931 54050737541701121713546397)
    ·
      refine ⟨20269026578137920642579899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54050737541701121713546397 20269026578137920642579899)
      ·
        refine ⟨30403539867206880963869849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20269026578137920642579899 30403539867206880963869849)
        ·
          refine ⟨22802654900405160722902387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30403539867206880963869849 22802654900405160722902387)
          ·
            refine ⟨34203982350607741084353581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22802654900405160722902387 34203982350607741084353581)
            ·
              refine ⟨12826493381477902906632593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34203982350607741084353581 12826493381477902906632593)
              ·
                refine ⟨9619870036108427179974445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12826493381477902906632593 9619870036108427179974445)
                ·
                  refine ⟨3607451263540660192490417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9619870036108427179974445 3607451263540660192490417)
                  ·
                    refine ⟨2705588447655495144367813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3607451263540660192490417 2705588447655495144367813)
                    ·
                      refine ⟨507297833935405339568965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2705588447655495144367813 507297833935405339568965)
                      ·
                        rfl

theorem cell23_987959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 2, 4].length) (baseStart_987959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_987959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_987959 prefixEnd_987959 := by exact prefixLift 987959
  have htrace : WordTrace (prefixWord ++ tailWord_987959) baseStart_987959 baseEnd_987959 := by
    simpa [prefixWord, tailWord_987959, baseEnd_987959] using wordTrace_append hprefix tailTrace_987959
  have hstable : (prefixWord ++ tailWord_987959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987959).length < 2 ^ (prefixWord ++ tailWord_987959).sum := by decide
  have hdescent : baseEnd_987959 < baseStart_987959 := by decide
  rcases family_descends (prefixWord ++ tailWord_987959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987976 : List Nat := [2, 1, 3, 1, 1, 3, 4, 1, 1, 2, 4]
def baseStart_987976 : Nat := 118140960795 + 987976 * 2 ^ 59
def prefixEnd_987976 : Nat := 4983230072969 + 3 ^ 40 * 987976 * 2
def baseEnd_987976 : Nat := 507306563106531773056387

theorem tailTrace_987976 : CollatzResearch.WordTrace tailWord_987976 prefixEnd_987976 507306563106531773056387 := by
  unfold tailWord_987976
  simp only [CollatzResearch.WordTrace]
  refine ⟨18017222534369579856199891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24022963379159439808266521 18017222534369579856199891)
  ·
    refine ⟨27025833801554369784299837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18017222534369579856199891 27025833801554369784299837)
    ·
      refine ⟨10134687675582888669112439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27025833801554369784299837 10134687675582888669112439)
      ·
        refine ⟨15202031513374333003668659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10134687675582888669112439 15202031513374333003668659)
        ·
          refine ⟨22803047270061499505502989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15202031513374333003668659 22803047270061499505502989)
          ·
            refine ⟨8551142726273062314563621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22803047270061499505502989 8551142726273062314563621)
            ·
              refine ⟨1603339261176199183980679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8551142726273062314563621 1603339261176199183980679)
              ·
                refine ⟨2405008891764298775971019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1603339261176199183980679 2405008891764298775971019)
                ·
                  refine ⟨3607513337646448163956529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2405008891764298775971019 3607513337646448163956529)
                  ·
                    refine ⟨2705635003234836122967397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3607513337646448163956529 2705635003234836122967397)
                    ·
                      refine ⟨507306563106531773056387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2705635003234836122967397 507306563106531773056387)
                      ·
                        rfl

theorem cell23_987976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 1, 2, 4].length) (baseStart_987976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_987976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_987976 prefixEnd_987976 := by exact prefixLift 987976
  have htrace : WordTrace (prefixWord ++ tailWord_987976) baseStart_987976 baseEnd_987976 := by
    simpa [prefixWord, tailWord_987976, baseEnd_987976] using wordTrace_append hprefix tailTrace_987976
  have hstable : (prefixWord ++ tailWord_987976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987976).length < 2 ^ (prefixWord ++ tailWord_987976).sum := by decide
  have hdescent : baseEnd_987976 < baseStart_987976 := by decide
  rcases family_descends (prefixWord ++ tailWord_987976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987980 : List Nat := [2, 2, 1, 3, 3, 2, 1, 2, 3, 2, 2]
def baseStart_987980 : Nat := 118140960795 + 987980 * 2 ^ 59
def prefixEnd_987980 : Nat := 4983230072969 + 3 ^ 40 * 987980 * 2
def baseEnd_987980 : Nat := 507308617029149757406369

theorem tailTrace_987980 : CollatzResearch.WordTrace tailWord_987980 prefixEnd_987980 507308617029149757406369 := by
  unfold tailWord_987980
  simp only [CollatzResearch.WordTrace]
  refine ⟨18017295480362334197772697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24023060640483112263696929 18017295480362334197772697)
  ·
    refine ⟨13512971610271750648329523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18017295480362334197772697 13512971610271750648329523)
    ·
      refine ⟨20269457415407625972494285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13512971610271750648329523 20269457415407625972494285)
      ·
        refine ⟨7601046530777859739685357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20269457415407625972494285 7601046530777859739685357)
        ·
          refine ⟨2850392449041697402382009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7601046530777859739685357 2850392449041697402382009)
          ·
            refine ⟨2137794336781273051786507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2850392449041697402382009 2137794336781273051786507)
            ·
              refine ⟨3206691505171909577679761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2137794336781273051786507 3206691505171909577679761)
              ·
                refine ⟨2405018628878932183259821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3206691505171909577679761 2405018628878932183259821)
                ·
                  refine ⟨901881985829599568722433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2405018628878932183259821 901881985829599568722433)
                  ·
                    refine ⟨676411489372199676541825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 901881985829599568722433 676411489372199676541825)
                    ·
                      refine ⟨507308617029149757406369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 676411489372199676541825 507308617029149757406369)
                      ·
                        rfl

theorem cell23_987980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 3, 2, 2].length) (baseStart_987980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_987980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_987980 prefixEnd_987980 := by exact prefixLift 987980
  have htrace : WordTrace (prefixWord ++ tailWord_987980) baseStart_987980 baseEnd_987980 := by
    simpa [prefixWord, tailWord_987980, baseEnd_987980] using wordTrace_append hprefix tailTrace_987980
  have hstable : (prefixWord ++ tailWord_987980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987980).length < 2 ^ (prefixWord ++ tailWord_987980).sum := by decide
  have hdescent : baseEnd_987980 < baseStart_987980 := by decide
  rcases family_descends (prefixWord ++ tailWord_987980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987986 : List Nat := [3, 2, 2, 1, 1, 2, 5, 7]
def baseStart_987986 : Nat := 118140960795 + 987986 * 2 ^ 59
def prefixEnd_987986 : Nat := 4983230072969 + 3 ^ 40 * 987986 * 2
def baseEnd_987986 : Nat := 18789322144928767923383

theorem tailTrace_987986 : CollatzResearch.WordTrace tailWord_987986 prefixEnd_987986 18789322144928767923383 := by
  unfold tailWord_987986
  simp only [CollatzResearch.WordTrace]
  refine ⟨9008702449675732855065953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24023206532468620946842541 9008702449675732855065953)
  ·
    refine ⟨6756526837256799641299465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9008702449675732855065953 6756526837256799641299465)
    ·
      refine ⟨5067395127942599730974599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6756526837256799641299465 5067395127942599730974599)
      ·
        refine ⟨7601092691913899596461899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5067395127942599730974599 7601092691913899596461899)
        ·
          refine ⟨11401639037870849394692849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7601092691913899596461899 11401639037870849394692849)
          ·
            refine ⟨8551229278403137046019637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11401639037870849394692849 8551229278403137046019637)
            ·
              refine ⟨801677744850294098064341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8551229278403137046019637 801677744850294098064341)
              ·
                refine ⟨18789322144928767923383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 801677744850294098064341 18789322144928767923383)
                ·
                  rfl

theorem cell23_987986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 7].length) (baseStart_987986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_987986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_987986 prefixEnd_987986 := by exact prefixLift 987986
  have htrace : WordTrace (prefixWord ++ tailWord_987986) baseStart_987986 baseEnd_987986 := by
    simpa [prefixWord, tailWord_987986, baseEnd_987986] using wordTrace_append hprefix tailTrace_987986
  have hstable : (prefixWord ++ tailWord_987986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987986).length < 2 ^ (prefixWord ++ tailWord_987986).sum := by decide
  have hdescent : baseEnd_987986 < baseStart_987986 := by decide
  rcases family_descends (prefixWord ++ tailWord_987986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988019 : List Nat := [1, 1, 1, 2, 2, 1, 4, 1, 1, 5, 4]
def baseStart_988019 : Nat := 118140960795 + 988019 * 2 ^ 59
def prefixEnd_988019 : Nat := 4983230072969 + 3 ^ 40 * 988019 * 2
def baseEnd_988019 : Nat := 507328642774675104818689

theorem tailTrace_988019 : CollatzResearch.WordTrace tailWord_988019 prefixEnd_988019 507328642774675104818689 := by
  unfold tailWord_988019
  simp only [CollatzResearch.WordTrace]
  refine ⟨36036013407583378056215111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24024008938388918704143407 36036013407583378056215111)
  ·
    refine ⟨54054020111375067084322667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36036013407583378056215111 54054020111375067084322667)
    ·
      refine ⟨81081030167062600626484001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54054020111375067084322667 81081030167062600626484001)
      ·
        refine ⟨60810772625296950469863001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81081030167062600626484001 60810772625296950469863001)
        ·
          refine ⟨45608079468972712852397251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60810772625296950469863001 45608079468972712852397251)
          ·
            refine ⟨68412119203459069278595877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45608079468972712852397251 68412119203459069278595877)
            ·
              refine ⟨12827272350648575489736727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68412119203459069278595877 12827272350648575489736727)
              ·
                refine ⟨19240908525972863234605091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12827272350648575489736727 19240908525972863234605091)
                ·
                  refine ⟨28861362788959294851907637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19240908525972863234605091 28861362788959294851907637)
                  ·
                    refine ⟨2705752761464933892366341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28861362788959294851907637 2705752761464933892366341)
                    ·
                      refine ⟨507328642774675104818689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2705752761464933892366341 507328642774675104818689)
                      ·
                        rfl

theorem cell23_988019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 5, 4].length) (baseStart_988019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_988019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_988019 prefixEnd_988019 := by exact prefixLift 988019
  have htrace : WordTrace (prefixWord ++ tailWord_988019) baseStart_988019 baseEnd_988019 := by
    simpa [prefixWord, tailWord_988019, baseEnd_988019] using wordTrace_append hprefix tailTrace_988019
  have hstable : (prefixWord ++ tailWord_988019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988019).length < 2 ^ (prefixWord ++ tailWord_988019).sum := by decide
  have hdescent : baseEnd_988019 < baseStart_988019 := by decide
  rcases family_descends (prefixWord ++ tailWord_988019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988034 : List Nat := [3, 4, 2, 2, 1, 1, 2, 2, 1, 2, 3]
def baseStart_988034 : Nat := 118140960795 + 988034 * 2 ^ 59
def prefixEnd_988034 : Nat := 4983230072969 + 3 ^ 40 * 988034 * 2
def baseEnd_988034 : Nat := 507336344984492546131121

theorem tailTrace_988034 : CollatzResearch.WordTrace tailWord_988034 prefixEnd_988034 507336344984492546131121 := by
  unfold tailWord_988034
  simp only [CollatzResearch.WordTrace]
  refine ⟨9009140125632258904502789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24024373668352690412007437 9009140125632258904502789)
  ·
    refine ⟨1689213773556048544594273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9009140125632258904502789 1689213773556048544594273)
    ·
      refine ⟨1266910330167036408445705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1689213773556048544594273 1266910330167036408445705)
      ·
        refine ⟨950182747625277306334279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1266910330167036408445705 950182747625277306334279)
        ·
          refine ⟨1425274121437915959501419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 950182747625277306334279 1425274121437915959501419)
          ·
            refine ⟨2137911182156873939252129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1425274121437915959501419 2137911182156873939252129)
            ·
              refine ⟨1603433386617655454439097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2137911182156873939252129 1603433386617655454439097)
              ·
                refine ⟨1202575039963241590829323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1603433386617655454439097 1202575039963241590829323)
                ·
                  refine ⟨1803862559944862386243985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1202575039963241590829323 1803862559944862386243985)
                  ·
                    refine ⟨1352896919958646789682989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1803862559944862386243985 1352896919958646789682989)
                    ·
                      refine ⟨507336344984492546131121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1352896919958646789682989 507336344984492546131121)
                      ·
                        rfl

theorem cell23_988034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_988034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_988034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_988034 prefixEnd_988034 := by exact prefixLift 988034
  have htrace : WordTrace (prefixWord ++ tailWord_988034) baseStart_988034 baseEnd_988034 := by
    simpa [prefixWord, tailWord_988034, baseEnd_988034] using wordTrace_append hprefix tailTrace_988034
  have hstable : (prefixWord ++ tailWord_988034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988034).length < 2 ^ (prefixWord ++ tailWord_988034).sum := by decide
  have hdescent : baseEnd_988034 < baseStart_988034 := by decide
  rcases family_descends (prefixWord ++ tailWord_988034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988040 : List Nat := [2, 1, 3, 3, 2, 1, 1, 4, 1, 3, 2]
def baseStart_988040 : Nat := 118140960795 + 988040 * 2 ^ 59
def prefixEnd_988040 : Nat := 4983230072969 + 3 ^ 40 * 988040 * 2
def baseEnd_988040 : Nat := 507339425868419522656093

theorem tailTrace_988040 : CollatzResearch.WordTrace tailWord_988040 prefixEnd_988040 507339425868419522656093 := by
  unfold tailWord_988040
  simp only [CollatzResearch.WordTrace]
  refine ⟨18018389670253649321364787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24024519560338199095153049 18018389670253649321364787)
  ·
    refine ⟨27027584505380473982047181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18018389670253649321364787 27027584505380473982047181)
    ·
      refine ⟨10135344189517677743267693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27027584505380473982047181 10135344189517677743267693)
      ·
        refine ⟨3800754071069129153725385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10135344189517677743267693 3800754071069129153725385)
        ·
          refine ⟨2850565553301846865294039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3800754071069129153725385 2850565553301846865294039)
          ·
            refine ⟨4275848329952770297941059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2850565553301846865294039 4275848329952770297941059)
            ·
              refine ⟨6413772494929155446911589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4275848329952770297941059 6413772494929155446911589)
              ·
                refine ⟨1202582342799216646295923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6413772494929155446911589 1202582342799216646295923)
                ·
                  refine ⟨1803873514198824969443885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1202582342799216646295923 1803873514198824969443885)
                  ·
                    refine ⟨676452567824559363541457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1803873514198824969443885 676452567824559363541457)
                    ·
                      refine ⟨507339425868419522656093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 676452567824559363541457 507339425868419522656093)
                      ·
                        rfl

theorem cell23_988040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_988040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_988040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_988040 prefixEnd_988040 := by exact prefixLift 988040
  have htrace : WordTrace (prefixWord ++ tailWord_988040) baseStart_988040 baseEnd_988040 := by
    simpa [prefixWord, tailWord_988040, baseEnd_988040] using wordTrace_append hprefix tailTrace_988040
  have hstable : (prefixWord ++ tailWord_988040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988040).length < 2 ^ (prefixWord ++ tailWord_988040).sum := by decide
  have hdescent : baseEnd_988040 < baseStart_988040 := by decide
  rcases family_descends (prefixWord ++ tailWord_988040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988079 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 8]
def baseStart_988079 : Nat := 118140960795 + 988079 * 2 ^ 59
def prefixEnd_988079 : Nat := 4983230072969 + 3 ^ 40 * 988079 * 2
def baseEnd_988079 : Nat := 507359451613944870068413

theorem tailTrace_988079 : CollatzResearch.WordTrace tailWord_988079 prefixEnd_988079 507359451613944870068413 := by
  unfold tailWord_988079
  simp only [CollatzResearch.WordTrace]
  refine ⟨36038201787366008303399291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24025467858244005535599527 36038201787366008303399291)
  ·
    refine ⟨54057302681049012455098937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36038201787366008303399291 54057302681049012455098937)
    ·
      refine ⟨40542977010786759341324203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54057302681049012455098937 40542977010786759341324203)
      ·
        refine ⟨60814465516180139011986305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40542977010786759341324203 60814465516180139011986305)
        ·
          refine ⟨45610849137135104258989729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60814465516180139011986305 45610849137135104258989729)
          ·
            refine ⟨34208136852851328194242297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45610849137135104258989729 34208136852851328194242297)
            ·
              refine ⟨25656102639638496145681723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34208136852851328194242297 25656102639638496145681723)
              ·
                refine ⟨38484153959457744218522585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25656102639638496145681723 38484153959457744218522585)
                ·
                  refine ⟨28863115469593308163891939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38484153959457744218522585 28863115469593308163891939)
                  ·
                    refine ⟨43294673204389962245837909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28863115469593308163891939 43294673204389962245837909)
                    ·
                      refine ⟨507359451613944870068413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 43294673204389962245837909 507359451613944870068413)
                      ·
                        rfl

theorem cell23_988079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 8].length) (baseStart_988079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_988079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_988079 prefixEnd_988079 := by exact prefixLift 988079
  have htrace : WordTrace (prefixWord ++ tailWord_988079) baseStart_988079 baseEnd_988079 := by
    simpa [prefixWord, tailWord_988079, baseEnd_988079] using wordTrace_append hprefix tailTrace_988079
  have hstable : (prefixWord ++ tailWord_988079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988079).length < 2 ^ (prefixWord ++ tailWord_988079).sum := by decide
  have hdescent : baseEnd_988079 < baseStart_988079 := by decide
  rcases family_descends (prefixWord ++ tailWord_988079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988087 : List Nat := [1, 1, 3, 1, 3, 1, 6, 1, 2, 2, 2]
def baseStart_988087 : Nat := 118140960795 + 988087 * 2 ^ 59
def prefixEnd_988087 : Nat := 4983230072969 + 3 ^ 40 * 988087 * 2
def baseEnd_988087 : Nat := 507363559459180838768377

theorem tailTrace_988087 : CollatzResearch.WordTrace tailWord_988087 prefixEnd_988087 507363559459180838768377 := by
  unfold tailWord_988087
  simp only [CollatzResearch.WordTrace]
  refine ⟨36038493571337025669690515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24025662380891350446460343 36038493571337025669690515)
  ·
    refine ⟨54057740357005538504535773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36038493571337025669690515 54057740357005538504535773)
    ·
      refine ⟨20271652633877076939200915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54057740357005538504535773 20271652633877076939200915)
      ·
        refine ⟨30407478950815615408801373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20271652633877076939200915 30407478950815615408801373)
        ·
          refine ⟨11402804606555855778300515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30407478950815615408801373 11402804606555855778300515)
          ·
            refine ⟨17104206909833783667450773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11402804606555855778300515 17104206909833783667450773)
            ·
              refine ⟨801759698898458609411755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17104206909833783667450773 801759698898458609411755)
              ·
                refine ⟨1202639548347687914117633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 801759698898458609411755 1202639548347687914117633)
                ·
                  refine ⟨901979661260765935588225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1202639548347687914117633 901979661260765935588225)
                  ·
                    refine ⟨676484745945574451691169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 901979661260765935588225 676484745945574451691169)
                    ·
                      refine ⟨507363559459180838768377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 676484745945574451691169 507363559459180838768377)
                      ·
                        rfl

theorem cell23_988087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 1, 2, 2, 2].length) (baseStart_988087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_988087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_988087 prefixEnd_988087 := by exact prefixLift 988087
  have htrace : WordTrace (prefixWord ++ tailWord_988087) baseStart_988087 baseEnd_988087 := by
    simpa [prefixWord, tailWord_988087, baseEnd_988087] using wordTrace_append hprefix tailTrace_988087
  have hstable : (prefixWord ++ tailWord_988087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988087).length < 2 ^ (prefixWord ++ tailWord_988087).sum := by decide
  have hdescent : baseEnd_988087 < baseStart_988087 := by decide
  rcases family_descends (prefixWord ++ tailWord_988087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988127 : List Nat := [1, 1, 2, 3, 5, 2, 2, 2, 5]
def baseStart_988127 : Nat := 118140960795 + 988127 * 2 ^ 59
def prefixEnd_988127 : Nat := 4983230072969 + 3 ^ 40 * 988127 * 2
def baseEnd_988127 : Nat := 56376010965040075807577

theorem tailTrace_988127 : CollatzResearch.WordTrace tailWord_988127 prefixEnd_988127 56376010965040075807577 := by
  unfold tailWord_988127
  simp only [CollatzResearch.WordTrace]
  refine ⟨36039952491192112501146635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24026634994128075000764423 36039952491192112501146635)
  ·
    refine ⟨54059928736788168751719953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36039952491192112501146635 54059928736788168751719953)
    ·
      refine ⟨40544946552591126563789965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54059928736788168751719953 40544946552591126563789965)
      ·
        refine ⟨15204354957221672461421237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40544946552591126563789965 15204354957221672461421237)
        ·
          refine ⟨1425408277239531793258241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15204354957221672461421237 1425408277239531793258241)
          ·
            refine ⟨1069056207929648844943681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1425408277239531793258241 1069056207929648844943681)
            ·
              refine ⟨801792155947236633707761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1069056207929648844943681 801792155947236633707761)
              ·
                refine ⟨601344116960427475280821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 801792155947236633707761 601344116960427475280821)
                ·
                  refine ⟨56376010965040075807577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 601344116960427475280821 56376010965040075807577)
                  ·
                    rfl

theorem cell23_988127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 2, 5].length) (baseStart_988127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_988127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_988127 prefixEnd_988127 := by exact prefixLift 988127
  have htrace : WordTrace (prefixWord ++ tailWord_988127) baseStart_988127 baseEnd_988127 := by
    simpa [prefixWord, tailWord_988127, baseEnd_988127] using wordTrace_append hprefix tailTrace_988127
  have hstable : (prefixWord ++ tailWord_988127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988127).length < 2 ^ (prefixWord ++ tailWord_988127).sum := by decide
  have hdescent : baseEnd_988127 < baseStart_988127 := by decide
  rcases family_descends (prefixWord ++ tailWord_988127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988143 : List Nat := [1, 1, 2, 1, 4, 3, 1, 1, 1, 6, 2]
def baseStart_988143 : Nat := 118140960795 + 988143 * 2 ^ 59
def prefixEnd_988143 : Nat := 4983230072969 + 3 ^ 40 * 988143 * 2
def baseEnd_988143 : Nat := 507392314375832619668119

theorem tailTrace_988143 : CollatzResearch.WordTrace tailWord_988143 prefixEnd_988143 507392314375832619668119 := by
  unfold tailWord_988143
  simp only [CollatzResearch.WordTrace]
  refine ⟨36040536059134147233729083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24027024039422764822486055 36040536059134147233729083)
  ·
    refine ⟨54060804088701220850593625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36040536059134147233729083 54060804088701220850593625)
    ·
      refine ⟨40545603066525915637945219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54060804088701220850593625 40545603066525915637945219)
      ·
        refine ⟨60818404599788873456917829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40545603066525915637945219 60818404599788873456917829)
        ·
          refine ⟨11403450862460413773172093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60818404599788873456917829 11403450862460413773172093)
          ·
            refine ⟨4276294073422655164939535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11403450862460413773172093 4276294073422655164939535)
            ·
              refine ⟨6414441110133982747409303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4276294073422655164939535 6414441110133982747409303)
              ·
                refine ⟨9621661665200974121113955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6414441110133982747409303 9621661665200974121113955)
                ·
                  refine ⟨14432492497801461181670933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9621661665200974121113955 14432492497801461181670933)
                  ·
                    refine ⟨676523085834443492890825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14432492497801461181670933 676523085834443492890825)
                    ·
                      refine ⟨507392314375832619668119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 676523085834443492890825 507392314375832619668119)
                      ·
                        rfl

theorem cell23_988143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 6, 2].length) (baseStart_988143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_988143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_988143 prefixEnd_988143 := by exact prefixLift 988143
  have htrace : WordTrace (prefixWord ++ tailWord_988143) baseStart_988143 baseEnd_988143 := by
    simpa [prefixWord, tailWord_988143, baseEnd_988143] using wordTrace_append hprefix tailTrace_988143
  have hstable : (prefixWord ++ tailWord_988143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988143).length < 2 ^ (prefixWord ++ tailWord_988143).sum := by decide
  have hdescent : baseEnd_988143 < baseStart_988143 := by decide
  rcases family_descends (prefixWord ++ tailWord_988143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988153 : List Nat := [1, 2, 1, 3, 1, 3, 3, 2, 3, 4]
def baseStart_988153 : Nat := 118140960795 + 988153 * 2 ^ 59
def prefixEnd_988153 : Nat := 4983230072969 + 3 ^ 40 * 988153 * 2
def baseEnd_988153 : Nat := 169132483060792526847691

theorem tailTrace_988153 : CollatzResearch.WordTrace tailWord_988153 prefixEnd_988153 169132483060792526847691 := by
  unfold tailWord_988153
  simp only [CollatzResearch.WordTrace]
  refine ⟨36040900789097918941593113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24027267192731945961062075 36040900789097918941593113)
  ·
    refine ⟨27030675591823439206194835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36040900789097918941593113 27030675591823439206194835)
    ·
      refine ⟨40546013387735158809292253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27030675591823439206194835 40546013387735158809292253)
      ·
        refine ⟨15204755020400684553484595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40546013387735158809292253 15204755020400684553484595)
        ·
          refine ⟨22807132530601026830226893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15204755020400684553484595 22807132530601026830226893)
          ·
            refine ⟨8552674698975385061335085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22807132530601026830226893 8552674698975385061335085)
            ·
              refine ⟨3207253012115769398000657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8552674698975385061335085 3207253012115769398000657)
              ·
                refine ⟨2405439759086827048500493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3207253012115769398000657 2405439759086827048500493)
                ·
                  refine ⟨902039909657560143187685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2405439759086827048500493 902039909657560143187685)
                  ·
                    refine ⟨169132483060792526847691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 902039909657560143187685 169132483060792526847691)
                    ·
                      rfl

theorem cell23_988153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 3, 4].length) (baseStart_988153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_988153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_988153 prefixEnd_988153 := by exact prefixLift 988153
  have htrace : WordTrace (prefixWord ++ tailWord_988153) baseStart_988153 baseEnd_988153 := by
    simpa [prefixWord, tailWord_988153, baseEnd_988153] using wordTrace_append hprefix tailTrace_988153
  have hstable : (prefixWord ++ tailWord_988153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988153).length < 2 ^ (prefixWord ++ tailWord_988153).sum := by decide
  have hdescent : baseEnd_988153 < baseStart_988153 := by decide
  rcases family_descends (prefixWord ++ tailWord_988153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988183 : List Nat := [1, 1, 3, 5, 1, 2, 1, 1, 8]
def baseStart_988183 : Nat := 118140960795 + 988183 * 2 ^ 59
def prefixEnd_988183 : Nat := 4983230072969 + 3 ^ 40 * 988183 * 2
def baseEnd_988183 : Nat := 56379205955779162574215

theorem tailTrace_988183 : CollatzResearch.WordTrace tailWord_988183 prefixEnd_988183 56379205955779162574215 := by
  unfold tailWord_988183
  simp only [CollatzResearch.WordTrace]
  refine ⟨36041994978989234065185203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24027996652659489376790135 36041994978989234065185203)
  ·
    refine ⟨54062992468483851097777805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36041994978989234065185203 54062992468483851097777805)
    ·
      refine ⟨20273622175681444161666677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54062992468483851097777805 20273622175681444161666677)
      ·
        refine ⟨1900652078970135390156251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20273622175681444161666677 1900652078970135390156251)
        ·
          refine ⟨2850978118455203085234377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1900652078970135390156251 2850978118455203085234377)
          ·
            refine ⟨2138233588841402313925783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2850978118455203085234377 2138233588841402313925783)
            ·
              refine ⟨3207350383262103470888675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2138233588841402313925783 3207350383262103470888675)
              ·
                refine ⟨4811025574893155206333013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3207350383262103470888675 4811025574893155206333013)
                ·
                  refine ⟨56379205955779162574215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4811025574893155206333013 56379205955779162574215)
                  ·
                    rfl

theorem cell23_988183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 8].length) (baseStart_988183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_988183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_988183 prefixEnd_988183 := by exact prefixLift 988183
  have htrace : WordTrace (prefixWord ++ tailWord_988183) baseStart_988183 baseEnd_988183 := by
    simpa [prefixWord, tailWord_988183, baseEnd_988183] using wordTrace_append hprefix tailTrace_988183
  have hstable : (prefixWord ++ tailWord_988183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988183).length < 2 ^ (prefixWord ++ tailWord_988183).sum := by decide
  have hdescent : baseEnd_988183 < baseStart_988183 := by decide
  rcases family_descends (prefixWord ++ tailWord_988183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988186 : List Nat := [3, 1, 1, 3, 1, 2, 1, 1, 1, 1, 8]
def baseStart_988186 : Nat := 118140960795 + 988186 * 2 ^ 59
def prefixEnd_988186 : Nat := 4983230072969 + 3 ^ 40 * 988186 * 2
def baseEnd_988186 : Nat := 507414394043975951430421

theorem tailTrace_988186 : CollatzResearch.WordTrace tailWord_988186 prefixEnd_988186 507414394043975951430421 := by
  unfold tailWord_988186
  simp only [CollatzResearch.WordTrace]
  refine ⟨9010526099494591394386103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24028069598652243718362941 9010526099494591394386103)
  ·
    refine ⟨13515789149241887091579155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9010526099494591394386103 13515789149241887091579155)
    ·
      refine ⟨20273683723862830637368733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13515789149241887091579155 20273683723862830637368733)
      ·
        refine ⟨7602631396448561489013275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20273683723862830637368733 7602631396448561489013275)
        ·
          refine ⟨11403947094672842233519913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7602631396448561489013275 11403947094672842233519913)
          ·
            refine ⟨8552960321004631675139935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11403947094672842233519913 8552960321004631675139935)
            ·
              refine ⟨12829440481506947512709903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8552960321004631675139935 12829440481506947512709903)
              ·
                refine ⟨19244160722260421269064855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12829440481506947512709903 19244160722260421269064855)
                ·
                  refine ⟨28866241083390631903597283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19244160722260421269064855 28866241083390631903597283)
                  ·
                    refine ⟨43299361625085947855395925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28866241083390631903597283 43299361625085947855395925)
                    ·
                      refine ⟨507414394043975951430421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 43299361625085947855395925 507414394043975951430421)
                      ·
                        rfl

theorem cell23_988186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_988186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_988186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_988186 prefixEnd_988186 := by exact prefixLift 988186
  have htrace : WordTrace (prefixWord ++ tailWord_988186) baseStart_988186 baseEnd_988186 := by
    simpa [prefixWord, tailWord_988186, baseEnd_988186] using wordTrace_append hprefix tailTrace_988186
  have hstable : (prefixWord ++ tailWord_988186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988186).length < 2 ^ (prefixWord ++ tailWord_988186).sum := by decide
  have hdescent : baseEnd_988186 < baseStart_988186 := by decide
  rcases family_descends (prefixWord ++ tailWord_988186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988203 : List Nat := [1, 1, 1, 1, 2, 1, 5, 1, 3, 5, 2]
def baseStart_988203 : Nat := 118140960795 + 988203 * 2 ^ 59
def prefixEnd_988203 : Nat := 4983230072969 + 3 ^ 40 * 988203 * 2
def baseEnd_988203 : Nat := 507423123215102384917843

theorem tailTrace_988203 : CollatzResearch.WordTrace tailWord_988203 prefixEnd_988203 507423123215102384917843 := by
  unfold tailWord_988203
  simp only [CollatzResearch.WordTrace]
  refine ⟨36042724438916777480913263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24028482959277851653942175 36042724438916777480913263)
  ·
    refine ⟨54064086658375166221369895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36042724438916777480913263 54064086658375166221369895)
    ·
      refine ⟨81096129987562749332054843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54064086658375166221369895 81096129987562749332054843)
      ·
        refine ⟨121644194981344123998082265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81096129987562749332054843 121644194981344123998082265)
        ·
          refine ⟨91233146236008092998561699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121644194981344123998082265 91233146236008092998561699)
          ·
            refine ⟨136849719354012139497842549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91233146236008092998561699 136849719354012139497842549)
            ·
              refine ⟨12829661189438638077922739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 136849719354012139497842549 12829661189438638077922739)
              ·
                refine ⟨19244491784157957116884109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12829661189438638077922739 19244491784157957116884109)
                ·
                  refine ⟨7216684419059233918831541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19244491784157957116884109 7216684419059233918831541)
                  ·
                    refine ⟨676564164286803179890457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7216684419059233918831541 676564164286803179890457)
                    ·
                      refine ⟨507423123215102384917843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 676564164286803179890457 507423123215102384917843)
                      ·
                        rfl

theorem cell23_988203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 5, 2].length) (baseStart_988203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_988203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_988203 prefixEnd_988203 := by exact prefixLift 988203
  have htrace : WordTrace (prefixWord ++ tailWord_988203) baseStart_988203 baseEnd_988203 := by
    simpa [prefixWord, tailWord_988203, baseEnd_988203] using wordTrace_append hprefix tailTrace_988203
  have hstable : (prefixWord ++ tailWord_988203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988203).length < 2 ^ (prefixWord ++ tailWord_988203).sum := by decide
  have hdescent : baseEnd_988203 < baseStart_988203 := by decide
  rcases family_descends (prefixWord ++ tailWord_988203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988210 : List Nat := [3, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3]
def baseStart_988210 : Nat := 118140960795 + 988210 * 2 ^ 59
def prefixEnd_988210 : Nat := 4983230072969 + 3 ^ 40 * 988210 * 2
def baseEnd_988210 : Nat := 507426717579683857530311

theorem tailTrace_988210 : CollatzResearch.WordTrace tailWord_988210 prefixEnd_988210 507426717579683857530311 := by
  unfold tailWord_988210
  simp only [CollatzResearch.WordTrace]
  refine ⟨9010744937472854419104521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24028653166594278450945389 9010744937472854419104521)
  ·
    refine ⟨6758058703104640814328391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9010744937472854419104521 6758058703104640814328391)
    ·
      refine ⟨10137088054656961221492587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6758058703104640814328391 10137088054656961221492587)
      ·
        refine ⟨15205632081985441832238881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10137088054656961221492587 15205632081985441832238881)
        ·
          refine ⟨11404224061489081374179161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15205632081985441832238881 11404224061489081374179161)
          ·
            refine ⟨8553168046116811030634371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11404224061489081374179161 8553168046116811030634371)
            ·
              refine ⟨12829752069175216545951557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8553168046116811030634371 12829752069175216545951557)
              ·
                refine ⟨2405578512970353102365917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12829752069175216545951557 2405578512970353102365917)
                ·
                  refine ⟨902091942363882413387219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2405578512970353102365917 902091942363882413387219)
                  ·
                    refine ⟨1353137913545823620080829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 902091942363882413387219 1353137913545823620080829)
                    ·
                      refine ⟨507426717579683857530311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1353137913545823620080829 507426717579683857530311)
                      ·
                        rfl

theorem cell23_988210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3].length) (baseStart_988210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_988210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_988210 prefixEnd_988210 := by exact prefixLift 988210
  have htrace : WordTrace (prefixWord ++ tailWord_988210) baseStart_988210 baseEnd_988210 := by
    simpa [prefixWord, tailWord_988210, baseEnd_988210] using wordTrace_append hprefix tailTrace_988210
  have hstable : (prefixWord ++ tailWord_988210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988210).length < 2 ^ (prefixWord ++ tailWord_988210).sum := by decide
  have hdescent : baseEnd_988210 < baseStart_988210 := by decide
  rcases family_descends (prefixWord ++ tailWord_988210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988220 : List Nat := [2, 2, 2, 2, 2, 2, 2, 1, 1, 5, 2]
def baseStart_988220 : Nat := 118140960795 + 988220 * 2 ^ 59
def prefixEnd_988220 : Nat := 4983230072969 + 3 ^ 40 * 988220 * 2
def baseEnd_988220 : Nat := 507431852386228818405265

theorem tailTrace_988220 : CollatzResearch.WordTrace tailWord_988220 prefixEnd_988220 507431852386228818405265 := by
  unfold tailWord_988220
  simp only [CollatzResearch.WordTrace]
  refine ⟨18021672239927594692141057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24028896319903459589521409 18021672239927594692141057)
  ·
    refine ⟨13516254179945696019105793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18021672239927594692141057 13516254179945696019105793)
    ·
      refine ⟨10137190634959272014329345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13516254179945696019105793 10137190634959272014329345)
      ·
        refine ⟨7602892976219454010747009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10137190634959272014329345 7602892976219454010747009)
        ·
          refine ⟨5702169732164590508060257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7602892976219454010747009 5702169732164590508060257)
          ·
            refine ⟨4276627299123442881045193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5702169732164590508060257 4276627299123442881045193)
            ·
              refine ⟨3207470474342582160783895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4276627299123442881045193 3207470474342582160783895)
              ·
                refine ⟨4811205711513873241175843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3207470474342582160783895 4811205711513873241175843)
                ·
                  refine ⟨7216808567270809861763765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4811205711513873241175843 7216808567270809861763765)
                  ·
                    refine ⟨676575803181638424540353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7216808567270809861763765 676575803181638424540353)
                    ·
                      refine ⟨507431852386228818405265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 676575803181638424540353 507431852386228818405265)
                      ·
                        rfl

theorem cell23_988220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 1, 5, 2].length) (baseStart_988220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_988220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_988220 prefixEnd_988220 := by exact prefixLift 988220
  have htrace : WordTrace (prefixWord ++ tailWord_988220) baseStart_988220 baseEnd_988220 := by
    simpa [prefixWord, tailWord_988220, baseEnd_988220] using wordTrace_append hprefix tailTrace_988220
  have hstable : (prefixWord ++ tailWord_988220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988220).length < 2 ^ (prefixWord ++ tailWord_988220).sum := by decide
  have hdescent : baseEnd_988220 < baseStart_988220 := by decide
  rcases family_descends (prefixWord ++ tailWord_988220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988237 : List Nat := [1, 6, 1, 1, 1, 2, 1, 1, 4, 3, 2]
def baseStart_988237 : Nat := 118140960795 + 988237 * 2 ^ 59
def prefixEnd_988237 : Nat := 4983230072969 + 3 ^ 40 * 988237 * 2
def baseEnd_988237 : Nat := 507440581557355251892687

theorem tailTrace_988237 : CollatzResearch.WordTrace tailWord_988237 prefixEnd_988237 507440581557355251892687 := by
  unfold tailWord_988237
  simp only [CollatzResearch.WordTrace]
  refine ⟨36043964520793601287650965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24029309680529067525100643 36043964520793601287650965)
  ·
    refine ⟨1689560836912200060358639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 36043964520793601287650965 1689560836912200060358639)
    ·
      refine ⟨2534341255368300090537959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1689560836912200060358639 2534341255368300090537959)
      ·
        refine ⟨3801511883052450135806939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2534341255368300090537959 3801511883052450135806939)
        ·
          refine ⟨5702267824578675203710409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3801511883052450135806939 5702267824578675203710409)
          ·
            refine ⟨4276700868434006402782807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5702267824578675203710409 4276700868434006402782807)
            ·
              refine ⟨6415051302651009604174211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4276700868434006402782807 6415051302651009604174211)
              ·
                refine ⟨9622576953976514406261317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6415051302651009604174211 9622576953976514406261317)
                ·
                  refine ⟨1804233178870596451173997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9622576953976514406261317 1804233178870596451173997)
                  ·
                    refine ⟨676587442076473669190249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1804233178870596451173997 676587442076473669190249)
                    ·
                      refine ⟨507440581557355251892687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 676587442076473669190249 507440581557355251892687)
                      ·
                        rfl

theorem cell23_988237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_988237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_988237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_988237 prefixEnd_988237 := by exact prefixLift 988237
  have htrace : WordTrace (prefixWord ++ tailWord_988237) baseStart_988237 baseEnd_988237 := by
    simpa [prefixWord, tailWord_988237, baseEnd_988237] using wordTrace_append hprefix tailTrace_988237
  have hstable : (prefixWord ++ tailWord_988237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988237).length < 2 ^ (prefixWord ++ tailWord_988237).sum := by decide
  have hdescent : baseEnd_988237 < baseStart_988237 := by decide
  rcases family_descends (prefixWord ++ tailWord_988237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988263 : List Nat := [1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 6]
def baseStart_988263 : Nat := 118140960795 + 988263 * 2 ^ 59
def prefixEnd_988263 : Nat := 4983230072969 + 3 ^ 40 * 988263 * 2
def baseEnd_988263 : Nat := 507453932054372150167567

theorem tailTrace_988263 : CollatzResearch.WordTrace tailWord_988263 prefixEnd_988263 507453932054372150167567 := by
  unfold tailWord_988263
  simp only [CollatzResearch.WordTrace]
  refine ⟨36044912818699407728097443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24029941879132938485398295 36044912818699407728097443)
  ·
    refine ⟨54067369228049111592146165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36044912818699407728097443 54067369228049111592146165)
    ·
      refine ⟨5068815865129604211763703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54067369228049111592146165 5068815865129604211763703)
      ·
        refine ⟨7603223797694406317645555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5068815865129604211763703 7603223797694406317645555)
        ·
          refine ⟨11404835696541609476468333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7603223797694406317645555 11404835696541609476468333)
          ·
            refine ⟨4276813386203103553675625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11404835696541609476468333 4276813386203103553675625)
            ·
              refine ⟨3207610039652327665256719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4276813386203103553675625 3207610039652327665256719)
              ·
                refine ⟨4811415059478491497885079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3207610039652327665256719 4811415059478491497885079)
                ·
                  refine ⟨7217122589217737246827619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4811415059478491497885079 7217122589217737246827619)
                  ·
                    refine ⟨10825683883826605870241429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7217122589217737246827619 10825683883826605870241429)
                    ·
                      refine ⟨507453932054372150167567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10825683883826605870241429 507453932054372150167567)
                      ·
                        rfl

theorem cell23_988263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_988263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_988263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_988263 prefixEnd_988263 := by exact prefixLift 988263
  have htrace : WordTrace (prefixWord ++ tailWord_988263) baseStart_988263 baseEnd_988263 := by
    simpa [prefixWord, tailWord_988263, baseEnd_988263] using wordTrace_append hprefix tailTrace_988263
  have hstable : (prefixWord ++ tailWord_988263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988263).length < 2 ^ (prefixWord ++ tailWord_988263).sum := by decide
  have hdescent : baseEnd_988263 < baseStart_988263 := by decide
  rcases family_descends (prefixWord ++ tailWord_988263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988264 : List Nat := [2, 1, 4, 4, 1, 2, 1, 2, 1, 5]
def baseStart_988264 : Nat := 118140960795 + 988264 * 2 ^ 59
def prefixEnd_988264 : Nat := 4983230072969 + 3 ^ 40 * 988264 * 2
def baseEnd_988264 : Nat := 169151481845008882085021

theorem tailTrace_988264 : CollatzResearch.WordTrace tailWord_988264 prefixEnd_988264 169151481845008882085021 := by
  unfold tailWord_988264
  simp only [CollatzResearch.WordTrace]
  refine ⟨18022474645847892449441923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24029966194463856599255897 18022474645847892449441923)
  ·
    refine ⟨27033711968771838674162885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18022474645847892449441923 27033711968771838674162885)
    ·
      refine ⟨5068820994144719751405541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27033711968771838674162885 5068820994144719751405541)
      ·
        refine ⟨950403936402134953388539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5068820994144719751405541 950403936402134953388539)
        ·
          refine ⟨1425605904603202430082809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 950403936402134953388539 1425605904603202430082809)
          ·
            refine ⟨1069204428452401822562107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1425605904603202430082809 1069204428452401822562107)
            ·
              refine ⟨1603806642678602733843161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1069204428452401822562107 1603806642678602733843161)
              ·
                refine ⟨1202854982008952050382371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1603806642678602733843161 1202854982008952050382371)
                ·
                  refine ⟨1804282473013428075573557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1202854982008952050382371 1804282473013428075573557)
                  ·
                    refine ⟨169151481845008882085021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1804282473013428075573557 169151481845008882085021)
                    ·
                      rfl

theorem cell23_988264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_988264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_988264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_988264 prefixEnd_988264 := by exact prefixLift 988264
  have htrace : WordTrace (prefixWord ++ tailWord_988264) baseStart_988264 baseEnd_988264 := by
    simpa [prefixWord, tailWord_988264, baseEnd_988264] using wordTrace_append hprefix tailTrace_988264
  have hstable : (prefixWord ++ tailWord_988264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988264).length < 2 ^ (prefixWord ++ tailWord_988264).sum := by decide
  have hdescent : baseEnd_988264 < baseStart_988264 := by decide
  rcases family_descends (prefixWord ++ tailWord_988264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988277 : List Nat := [1, 3, 4, 3, 1, 1, 1, 2, 1, 6]
def baseStart_988277 : Nat := 118140960795 + 988277 * 2 ^ 59
def prefixEnd_988277 : Nat := 4983230072969 + 3 ^ 40 * 988277 * 2
def baseEnd_988277 : Nat := 169153706927845031797501

theorem tailTrace_988277 : CollatzResearch.WordTrace tailWord_988277 prefixEnd_988277 169153706927845031797501 := by
  unfold tailWord_988277
  simp only [CollatzResearch.WordTrace]
  refine ⟨36045423440648688119107085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24030282293765792079404723 36045423440648688119107085)
  ·
    refine ⟨13517033790243258044665157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36045423440648688119107085 13517033790243258044665157)
    ·
      refine ⟨2534443835670610883374717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13517033790243258044665157 2534443835670610883374717)
      ·
        refine ⟨950416438376479081265519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2534443835670610883374717 950416438376479081265519)
        ·
          refine ⟨1425624657564718621898279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 950416438376479081265519 1425624657564718621898279)
          ·
            refine ⟨2138436986347077932847419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1425624657564718621898279 2138436986347077932847419)
            ·
              refine ⟨3207655479520616899271129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2138436986347077932847419 3207655479520616899271129)
              ·
                refine ⟨2405741609640462674453347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3207655479520616899271129 2405741609640462674453347)
                ·
                  refine ⟨3608612414460694011680021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2405741609640462674453347 3608612414460694011680021)
                  ·
                    refine ⟨169153706927845031797501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3608612414460694011680021 169153706927845031797501)
                    ·
                      rfl

theorem cell23_988277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_988277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_988277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_988277 prefixEnd_988277 := by exact prefixLift 988277
  have htrace : WordTrace (prefixWord ++ tailWord_988277) baseStart_988277 baseEnd_988277 := by
    simpa [prefixWord, tailWord_988277, baseEnd_988277] using wordTrace_append hprefix tailTrace_988277
  have hstable : (prefixWord ++ tailWord_988277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988277).length < 2 ^ (prefixWord ++ tailWord_988277).sum := by decide
  have hdescent : baseEnd_988277 < baseStart_988277 := by decide
  rcases family_descends (prefixWord ++ tailWord_988277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988284 : List Nat := [2, 2, 2, 1, 1, 3, 2, 5, 1, 2, 2]
def baseStart_988284 : Nat := 118140960795 + 988284 * 2 ^ 59
def prefixEnd_988284 : Nat := 4983230072969 + 3 ^ 40 * 988284 * 2
def baseEnd_988284 : Nat := 507464715148116568004971

theorem tailTrace_988284 : CollatzResearch.WordTrace tailWord_988284 prefixEnd_988284 507464715148116568004971 := by
  unfold tailWord_988284
  simp only [CollatzResearch.WordTrace]
  refine ⟨18022839375811664157305953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24030452501082218876407937 18022839375811664157305953)
  ·
    refine ⟨13517129531858748117979465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18022839375811664157305953 13517129531858748117979465)
    ·
      refine ⟨10137847148894061088484599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13517129531858748117979465 10137847148894061088484599)
      ·
        refine ⟨15206770723341091632726899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10137847148894061088484599 15206770723341091632726899)
        ·
          refine ⟨22810156085011637449090349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15206770723341091632726899 22810156085011637449090349)
          ·
            refine ⟨8553808531879364043408881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22810156085011637449090349 8553808531879364043408881)
            ·
              refine ⟨6415356398909523032556661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8553808531879364043408881 6415356398909523032556661)
              ·
                refine ⟨601439662397767784302187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6415356398909523032556661 601439662397767784302187)
                ·
                  refine ⟨902159493596651676453281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 601439662397767784302187 902159493596651676453281)
                  ·
                    refine ⟨676619620197488757339961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 902159493596651676453281 676619620197488757339961)
                    ·
                      refine ⟨507464715148116568004971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 676619620197488757339961 507464715148116568004971)
                      ·
                        rfl

theorem cell23_988284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 5, 1, 2, 2].length) (baseStart_988284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_988284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_988284 prefixEnd_988284 := by exact prefixLift 988284
  have htrace : WordTrace (prefixWord ++ tailWord_988284) baseStart_988284 baseEnd_988284 := by
    simpa [prefixWord, tailWord_988284, baseEnd_988284] using wordTrace_append hprefix tailTrace_988284
  have hstable : (prefixWord ++ tailWord_988284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988284).length < 2 ^ (prefixWord ++ tailWord_988284).sum := by decide
  have hdescent : baseEnd_988284 < baseStart_988284 := by decide
  rcases family_descends (prefixWord ++ tailWord_988284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988300 : List Nat := [2, 2, 1, 2, 1, 1, 1, 5, 4, 1, 3]
def baseStart_988300 : Nat := 118140960795 + 988300 * 2 ^ 59
def prefixEnd_988300 : Nat := 4983230072969 + 3 ^ 40 * 988300 * 2
def baseEnd_988300 : Nat := 507472930838588505404897

theorem tailTrace_988300 : CollatzResearch.WordTrace tailWord_988300 prefixEnd_988300 507472930838588505404897 := by
  unfold tailWord_988300
  simp only [CollatzResearch.WordTrace]
  refine ⟨18023131159782681523597177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24030841546376908698129569 18023131159782681523597177)
  ·
    refine ⟨13517348369837011142697883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18023131159782681523597177 13517348369837011142697883)
    ·
      refine ⟨20276022554755516714046825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13517348369837011142697883 20276022554755516714046825)
      ·
        refine ⟨15207016916066637535535119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20276022554755516714046825 15207016916066637535535119)
        ·
          refine ⟨22810525374099956303302679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15207016916066637535535119 22810525374099956303302679)
          ·
            refine ⟨34215788061149934454954019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22810525374099956303302679 34215788061149934454954019)
            ·
              refine ⟨51323682091724901682431029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34215788061149934454954019 51323682091724901682431029)
              ·
                refine ⟨4811595196099209532727909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51323682091724901682431029 4811595196099209532727909)
                ·
                  refine ⟨902174099268601787386483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4811595196099209532727909 902174099268601787386483)
                  ·
                    refine ⟨1353261148902902681079725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 902174099268601787386483 1353261148902902681079725)
                    ·
                      refine ⟨507472930838588505404897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1353261148902902681079725 507472930838588505404897)
                      ·
                        rfl

theorem cell23_988300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 4, 1, 3].length) (baseStart_988300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_988300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_988300 prefixEnd_988300 := by exact prefixLift 988300
  have htrace : WordTrace (prefixWord ++ tailWord_988300) baseStart_988300 baseEnd_988300 := by
    simpa [prefixWord, tailWord_988300, baseEnd_988300] using wordTrace_append hprefix tailTrace_988300
  have hstable : (prefixWord ++ tailWord_988300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988300).length < 2 ^ (prefixWord ++ tailWord_988300).sum := by decide
  have hdescent : baseEnd_988300 < baseStart_988300 := by decide
  rcases family_descends (prefixWord ++ tailWord_988300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988317 : List Nat := [1, 4, 2, 1, 1, 2, 1, 5, 2, 1, 3]
def baseStart_988317 : Nat := 118140960795 + 988317 * 2 ^ 59
def prefixEnd_988317 : Nat := 4983230072969 + 3 ^ 40 * 988317 * 2
def baseEnd_988317 : Nat := 507481660009714938892319

theorem tailTrace_988317 : CollatzResearch.WordTrace tailWord_988317 prefixEnd_988317 507481660009714938892319 := by
  unfold tailWord_988317
  simp only [CollatzResearch.WordTrace]
  refine ⟨36046882360503774950563205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24031254907002516633708803 36046882360503774950563205)
  ·
    refine ⟨6758790442594457803230601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36046882360503774950563205 6758790442594457803230601)
    ·
      refine ⟨5069092831945843352422951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6758790442594457803230601 5069092831945843352422951)
      ·
        refine ⟨7603639247918765028634427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5069092831945843352422951 7603639247918765028634427)
        ·
          refine ⟨11405458871878147542951641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7603639247918765028634427 11405458871878147542951641)
          ·
            refine ⟨8554094153908610657213731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11405458871878147542951641 8554094153908610657213731)
            ·
              refine ⟨12831141230862915985820597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8554094153908610657213731 12831141230862915985820597)
              ·
                refine ⟨1202919490393398373670681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12831141230862915985820597 1202919490393398373670681)
                ·
                  refine ⟨902189617795048780253011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1202919490393398373670681 902189617795048780253011)
                  ·
                    refine ⟨1353284426692573170379517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 902189617795048780253011 1353284426692573170379517)
                    ·
                      refine ⟨507481660009714938892319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1353284426692573170379517 507481660009714938892319)
                      ·
                        rfl

theorem cell23_988317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_988317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_988317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_988317 prefixEnd_988317 := by exact prefixLift 988317
  have htrace : WordTrace (prefixWord ++ tailWord_988317) baseStart_988317 baseEnd_988317 := by
    simpa [prefixWord, tailWord_988317, baseEnd_988317] using wordTrace_append hprefix tailTrace_988317
  have hstable : (prefixWord ++ tailWord_988317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988317).length < 2 ^ (prefixWord ++ tailWord_988317).sum := by decide
  have hdescent : baseEnd_988317 < baseStart_988317 := by decide
  rcases family_descends (prefixWord ++ tailWord_988317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988343 : List Nat := [1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 5]
def baseStart_988343 : Nat := 118140960795 + 988343 * 2 ^ 59
def prefixEnd_988343 : Nat := 4983230072969 + 3 ^ 40 * 988343 * 2
def baseEnd_988343 : Nat := 507495010506731837167199

theorem tailTrace_988343 : CollatzResearch.WordTrace tailWord_988343 prefixEnd_988343 507495010506731837167199 := by
  unfold tailWord_988343
  simp only [CollatzResearch.WordTrace]
  refine ⟨36047830658409581391009683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24031887105606387594006455 36047830658409581391009683)
  ·
    refine ⟨54071745987614372086514525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36047830658409581391009683 54071745987614372086514525)
    ·
      refine ⟨20276904745355389532442947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54071745987614372086514525 20276904745355389532442947)
      ·
        refine ⟨30415357118033084298664421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20276904745355389532442947 30415357118033084298664421)
        ·
          refine ⟨5702879459631203305999579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30415357118033084298664421 5702879459631203305999579)
          ·
            refine ⟨8554319189446804958999369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5702879459631203305999579 8554319189446804958999369)
            ·
              refine ⟨6415739392085103719249527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8554319189446804958999369 6415739392085103719249527)
              ·
                refine ⟨9623609088127655578874291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6415739392085103719249527 9623609088127655578874291)
                ·
                  refine ⟨14435413632191483368311437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9623609088127655578874291 14435413632191483368311437)
                  ·
                    refine ⟨5413280112071806263116789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14435413632191483368311437 5413280112071806263116789)
                    ·
                      refine ⟨507495010506731837167199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5413280112071806263116789 507495010506731837167199)
                      ·
                        rfl

theorem cell23_988343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 5].length) (baseStart_988343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_988343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_988343 prefixEnd_988343 := by exact prefixLift 988343
  have htrace : WordTrace (prefixWord ++ tailWord_988343) baseStart_988343 baseEnd_988343 := by
    simpa [prefixWord, tailWord_988343, baseEnd_988343] using wordTrace_append hprefix tailTrace_988343
  have hstable : (prefixWord ++ tailWord_988343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988343).length < 2 ^ (prefixWord ++ tailWord_988343).sum := by decide
  have hdescent : baseEnd_988343 < baseStart_988343 := by decide
  rcases family_descends (prefixWord ++ tailWord_988343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988350 : List Nat := [4, 2, 1, 1, 3, 1, 1, 2, 2, 6]
def baseStart_988350 : Nat := 118140960795 + 988350 * 2 ^ 59
def prefixEnd_988350 : Nat := 4983230072969 + 3 ^ 40 * 988350 * 2
def baseEnd_988350 : Nat := 169166201623771103259889

theorem tailTrace_988350 : CollatzResearch.WordTrace tailWord_988350 prefixEnd_988350 169166201623771103259889 := by
  unfold tailWord_988350
  simp only [CollatzResearch.WordTrace]
  refine ⟨4506010746173027698314313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24032057312922814391009669 4506010746173027698314313)
  ·
    refine ⟨3379508059629770773735735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4506010746173027698314313 3379508059629770773735735)
    ·
      refine ⟨5069262089444656160603603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3379508059629770773735735 5069262089444656160603603)
      ·
        refine ⟨7603893134166984240905405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5069262089444656160603603 7603893134166984240905405)
        ·
          refine ⟨2851459925312619090339527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7603893134166984240905405 2851459925312619090339527)
          ·
            refine ⟨4277189887968928635509291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2851459925312619090339527 4277189887968928635509291)
            ·
              refine ⟨6415784831953392953263937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4277189887968928635509291 6415784831953392953263937)
              ·
                refine ⟨4811838623965044714947953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6415784831953392953263937 4811838623965044714947953)
                ·
                  refine ⟨3608878967973783536210965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4811838623965044714947953 3608878967973783536210965)
                  ·
                    refine ⟨169166201623771103259889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3608878967973783536210965 169166201623771103259889)
                    ·
                      rfl

theorem cell23_988350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_988350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_988350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_988350 prefixEnd_988350 := by exact prefixLift 988350
  have htrace : WordTrace (prefixWord ++ tailWord_988350) baseStart_988350 baseEnd_988350 := by
    simpa [prefixWord, tailWord_988350, baseEnd_988350] using wordTrace_append hprefix tailTrace_988350
  have hstable : (prefixWord ++ tailWord_988350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988350).length < 2 ^ (prefixWord ++ tailWord_988350).sum := by decide
  have hdescent : baseEnd_988350 < baseStart_988350 := by decide
  rcases family_descends (prefixWord ++ tailWord_988350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988370 : List Nat := [3, 2, 2, 2, 1, 1, 1, 3, 2, 2, 4]
def baseStart_988370 : Nat := 118140960795 + 988370 * 2 ^ 59
def prefixEnd_988370 : Nat := 4983230072969 + 3 ^ 40 * 988370 * 2
def baseEnd_988370 : Nat := 507508874484403231529575

theorem tailTrace_988370 : CollatzResearch.WordTrace tailWord_988370 prefixEnd_988370 507508874484403231529575 := by
  unfold tailWord_988370
  simp only [CollatzResearch.WordTrace]
  refine ⟨9012203857327941250560641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24032543619541176668161709 9012203857327941250560641)
  ·
    refine ⟨6759152892995955937920481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9012203857327941250560641 6759152892995955937920481)
    ·
      refine ⟨5069364669746966953440361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6759152892995955937920481 5069364669746966953440361)
      ·
        refine ⟨3802023502310225215080271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5069364669746966953440361 3802023502310225215080271)
        ·
          refine ⟨5703035253465337822620407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3802023502310225215080271 5703035253465337822620407)
          ·
            refine ⟨8554552880198006733930611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5703035253465337822620407 8554552880198006733930611)
            ·
              refine ⟨12831829320297010100895917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8554552880198006733930611 12831829320297010100895917)
              ·
                refine ⟨4811935995111378787835969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12831829320297010100895917 4811935995111378787835969)
                ·
                  refine ⟨3608951996333534090876977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4811935995111378787835969 3608951996333534090876977)
                  ·
                    refine ⟨2706713997250150568157733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3608951996333534090876977 2706713997250150568157733)
                    ·
                      refine ⟨507508874484403231529575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2706713997250150568157733 507508874484403231529575)
                      ·
                        rfl

theorem cell23_988370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_988370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_988370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_988370 prefixEnd_988370 := by exact prefixLift 988370
  have htrace : WordTrace (prefixWord ++ tailWord_988370) baseStart_988370 baseEnd_988370 := by
    simpa [prefixWord, tailWord_988370, baseEnd_988370] using wordTrace_append hprefix tailTrace_988370
  have hstable : (prefixWord ++ tailWord_988370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988370).length < 2 ^ (prefixWord ++ tailWord_988370).sum := by decide
  have hdescent : baseEnd_988370 < baseStart_988370 := by decide
  rcases family_descends (prefixWord ++ tailWord_988370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988400 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 3, 7, 2]
def baseStart_988400 : Nat := 118140960795 + 988400 * 2 ^ 59
def prefixEnd_988400 : Nat := 4983230072969 + 3 ^ 40 * 988400 * 2
def baseEnd_988400 : Nat := 507524278904038114154437

theorem tailTrace_988400 : CollatzResearch.WordTrace tailWord_988400 prefixEnd_988400 507524278904038114154437 := by
  unfold tailWord_988400
  simp only [CollatzResearch.WordTrace]
  refine ⟨18024954809601540062917327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24033273079468720083889769 18024954809601540062917327)
  ·
    refine ⟨27037432214402310094375991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18024954809601540062917327 27037432214402310094375991)
    ·
      refine ⟨40556148321603465141563987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27037432214402310094375991 40556148321603465141563987)
      ·
        refine ⟨60834222482405197712345981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40556148321603465141563987 60834222482405197712345981)
        ·
          refine ⟨22812833430901949142129743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60834222482405197712345981 22812833430901949142129743)
          ·
            refine ⟨34219250146352923713194615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22812833430901949142129743 34219250146352923713194615)
            ·
              refine ⟨51328875219529385569791923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34219250146352923713194615 51328875219529385569791923)
              ·
                refine ⟨76993312829294078354687885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51328875219529385569791923 76993312829294078354687885)
                ·
                  refine ⟨28872492310985279383007957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76993312829294078354687885 28872492310985279383007957)
                  ·
                    refine ⟨676699038538717485539249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28872492310985279383007957 676699038538717485539249)
                    ·
                      refine ⟨507524278904038114154437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 676699038538717485539249 507524278904038114154437)
                      ·
                        rfl

theorem cell23_988400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 3, 7, 2].length) (baseStart_988400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_988400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_988400 prefixEnd_988400 := by exact prefixLift 988400
  have htrace : WordTrace (prefixWord ++ tailWord_988400) baseStart_988400 baseEnd_988400 := by
    simpa [prefixWord, tailWord_988400, baseEnd_988400] using wordTrace_append hprefix tailTrace_988400
  have hstable : (prefixWord ++ tailWord_988400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988400).length < 2 ^ (prefixWord ++ tailWord_988400).sum := by decide
  have hdescent : baseEnd_988400 < baseStart_988400 := by decide
  rcases family_descends (prefixWord ++ tailWord_988400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988410 : List Nat := [3, 1, 1, 1, 1, 4, 3, 2, 2, 5]
def baseStart_988410 : Nat := 118140960795 + 988410 * 2 ^ 59
def prefixEnd_988410 : Nat := 4983230072969 + 3 ^ 40 * 988410 * 2
def baseEnd_988410 : Nat := 169176471236861025009797

theorem tailTrace_988410 : CollatzResearch.WordTrace tailWord_988410 prefixEnd_988410 169176471236861025009797 := by
  unfold tailWord_988410
  simp only [CollatzResearch.WordTrace]
  refine ⟨9012568587291712958424671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24033516232777901222465789 9012568587291712958424671)
  ·
    refine ⟨13518852880937569437637007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9012568587291712958424671 13518852880937569437637007)
    ·
      refine ⟨20278279321406354156455511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13518852880937569437637007 20278279321406354156455511)
      ·
        refine ⟨30417418982109531234683267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20278279321406354156455511 30417418982109531234683267)
        ·
          refine ⟨45626128473164296852024901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30417418982109531234683267 45626128473164296852024901)
          ·
            refine ⟨8554899088718305659754669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45626128473164296852024901 8554899088718305659754669)
            ·
              refine ⟨3208087158269364622408001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8554899088718305659754669 3208087158269364622408001)
              ·
                refine ⟨2406065368702023466806001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3208087158269364622408001 2406065368702023466806001)
                ·
                  refine ⟨1804549026526517600104501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2406065368702023466806001 1804549026526517600104501)
                  ·
                    refine ⟨169176471236861025009797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1804549026526517600104501 169176471236861025009797)
                    ·
                      rfl

theorem cell23_988410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 2, 5].length) (baseStart_988410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_988410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_988410 prefixEnd_988410 := by exact prefixLift 988410
  have htrace : WordTrace (prefixWord ++ tailWord_988410) baseStart_988410 baseEnd_988410 := by
    simpa [prefixWord, tailWord_988410, baseEnd_988410] using wordTrace_append hprefix tailTrace_988410
  have hstable : (prefixWord ++ tailWord_988410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988410).length < 2 ^ (prefixWord ++ tailWord_988410).sum := by decide
  have hdescent : baseEnd_988410 < baseStart_988410 := by decide
  rcases family_descends (prefixWord ++ tailWord_988410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988413 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 2, 2, 8]
def baseStart_988413 : Nat := 118140960795 + 988413 * 2 ^ 59
def prefixEnd_988413 : Nat := 4983230072969 + 3 ^ 40 * 988413 * 2
def baseEnd_988413 : Nat := 507530954152546563291877

theorem tailTrace_988413 : CollatzResearch.WordTrace tailWord_988413 prefixEnd_988413 507530954152546563291877 := by
  unfold tailWord_988413
  simp only [CollatzResearch.WordTrace]
  refine ⟨36050383768155983346057893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24033589178770655564038595 36050383768155983346057893)
  ·
    refine ⟨6759446956529246877385855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36050383768155983346057893 6759446956529246877385855)
    ·
      refine ⟨10139170434793870316078783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6759446956529246877385855 10139170434793870316078783)
      ·
        refine ⟨15208755652190805474118175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10139170434793870316078783 15208755652190805474118175)
        ·
          refine ⟨22813133478286208211177263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15208755652190805474118175 22813133478286208211177263)
          ·
            refine ⟨34219700217429312316765895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22813133478286208211177263 34219700217429312316765895)
            ·
              refine ⟨51329550326143968475148843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34219700217429312316765895 51329550326143968475148843)
              ·
                refine ⟨76994325489215952712723265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51329550326143968475148843 76994325489215952712723265)
                ·
                  refine ⟨57745744116911964534542449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76994325489215952712723265 57745744116911964534542449)
                  ·
                    refine ⟨43309308087683973400906837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57745744116911964534542449 43309308087683973400906837)
                    ·
                      refine ⟨507530954152546563291877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 43309308087683973400906837 507530954152546563291877)
                      ·
                        rfl

theorem cell23_988413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_988413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_988413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_988413 prefixEnd_988413 := by exact prefixLift 988413
  have htrace : WordTrace (prefixWord ++ tailWord_988413) baseStart_988413 baseEnd_988413 := by
    simpa [prefixWord, tailWord_988413, baseEnd_988413] using wordTrace_append hprefix tailTrace_988413
  have hstable : (prefixWord ++ tailWord_988413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988413).length < 2 ^ (prefixWord ++ tailWord_988413).sum := by decide
  have hdescent : baseEnd_988413 < baseStart_988413 := by decide
  rcases family_descends (prefixWord ++ tailWord_988413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988420 : List Nat := [2, 3, 2, 2, 2, 1, 1, 1, 1, 1, 7]
def baseStart_988420 : Nat := 118140960795 + 988420 * 2 ^ 59
def prefixEnd_988420 : Nat := 4983230072969 + 3 ^ 40 * 988420 * 2
def baseEnd_988420 : Nat := 507534548517128035904345

theorem tailTrace_988420 : CollatzResearch.WordTrace tailWord_988420 prefixEnd_988420 507534548517128035904345 := by
  unfold tailWord_988420
  simp only [CollatzResearch.WordTrace]
  refine ⟨18025319539565311770781357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24033759386087082361041809 18025319539565311770781357)
  ·
    refine ⟨6759494827336991914043009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18025319539565311770781357 6759494827336991914043009)
    ·
      refine ⟨5069621120502743935532257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6759494827336991914043009 5069621120502743935532257)
      ·
        refine ⟨3802215840377057951649193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5069621120502743935532257 3802215840377057951649193)
        ·
          refine ⟨2851661880282793463736895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3802215840377057951649193 2851661880282793463736895)
          ·
            refine ⟨4277492820424190195605343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2851661880282793463736895 4277492820424190195605343)
            ·
              refine ⟨6416239230636285293408015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4277492820424190195605343 6416239230636285293408015)
              ·
                refine ⟨9624358845954427940112023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6416239230636285293408015 9624358845954427940112023)
                ·
                  refine ⟨14436538268931641910168035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9624358845954427940112023 14436538268931641910168035)
                  ·
                    refine ⟨21654807403397462865252053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14436538268931641910168035 21654807403397462865252053)
                    ·
                      refine ⟨507534548517128035904345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 21654807403397462865252053 507534548517128035904345)
                      ·
                        rfl

theorem cell23_988420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_988420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_988420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_988420 prefixEnd_988420 := by exact prefixLift 988420
  have htrace : WordTrace (prefixWord ++ tailWord_988420) baseStart_988420 baseEnd_988420 := by
    simpa [prefixWord, tailWord_988420, baseEnd_988420] using wordTrace_append hprefix tailTrace_988420
  have hstable : (prefixWord ++ tailWord_988420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988420).length < 2 ^ (prefixWord ++ tailWord_988420).sum := by decide
  have hdescent : baseEnd_988420 < baseStart_988420 := by decide
  rcases family_descends (prefixWord ++ tailWord_988420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988443 : List Nat := [1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 6]
def baseStart_988443 : Nat := 118140960795 + 988443 * 2 ^ 59
def prefixEnd_988443 : Nat := 4983230072969 + 3 ^ 40 * 988443 * 2
def baseEnd_988443 : Nat := 507546358572181445916739

theorem tailTrace_988443 : CollatzResearch.WordTrace tailWord_988443 prefixEnd_988443 507546358572181445916739 := by
  unfold tailWord_988443
  simp only [CollatzResearch.WordTrace]
  refine ⟨36051477958047298469649983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24034318638698198979766655 36051477958047298469649983)
  ·
    refine ⟨54077216937070947704474975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36051477958047298469649983 54077216937070947704474975)
    ·
      refine ⟨81115825405606421556712463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54077216937070947704474975 81115825405606421556712463)
      ·
        refine ⟨121673738108409632335068695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81115825405606421556712463 121673738108409632335068695)
        ·
          refine ⟨182510607162614448502603043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121673738108409632335068695 182510607162614448502603043)
          ·
            refine ⟨273765910743921672753904565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182510607162614448502603043 273765910743921672753904565)
            ·
              refine ⟨25665554132242656820678553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 273765910743921672753904565 25665554132242656820678553)
              ·
                refine ⟨19249165599181992615508915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25665554132242656820678553 19249165599181992615508915)
                ·
                  refine ⟨28873748398772988923263373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19249165599181992615508915 28873748398772988923263373)
                  ·
                    refine ⟨10827655649539870846223765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28873748398772988923263373 10827655649539870846223765)
                    ·
                      refine ⟨507546358572181445916739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10827655649539870846223765 507546358572181445916739)
                      ·
                        rfl

theorem cell23_988443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 6].length) (baseStart_988443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_988443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_988443 prefixEnd_988443 := by exact prefixLift 988443
  have htrace : WordTrace (prefixWord ++ tailWord_988443) baseStart_988443 baseEnd_988443 := by
    simpa [prefixWord, tailWord_988443, baseEnd_988443] using wordTrace_append hprefix tailTrace_988443
  have hstable : (prefixWord ++ tailWord_988443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988443).length < 2 ^ (prefixWord ++ tailWord_988443).sum := by decide
  have hdescent : baseEnd_988443 < baseStart_988443 := by decide
  rcases family_descends (prefixWord ++ tailWord_988443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988467 : List Nat := [1, 1, 1, 2, 5, 2, 2, 2, 2, 2, 3]
def baseStart_988467 : Nat := 118140960795 + 988467 * 2 ^ 59
def prefixEnd_988467 : Nat := 4983230072969 + 3 ^ 40 * 988467 * 2
def baseEnd_988467 : Nat := 507558682107889352016629

theorem tailTrace_988467 : CollatzResearch.WordTrace tailWord_988467 prefixEnd_988467 507558682107889352016629 := by
  unfold tailWord_988467
  simp only [CollatzResearch.WordTrace]
  refine ⟨36052353309960350568523655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24034902206640233712349103 36052353309960350568523655)
  ·
    refine ⟨54078529964940525852785483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36052353309960350568523655 54078529964940525852785483)
    ·
      refine ⟨81117794947410788779178225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54078529964940525852785483 81117794947410788779178225)
      ·
        refine ⟨60838346210558091584383669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81117794947410788779178225 60838346210558091584383669)
        ·
          refine ⟨5703594957239821086035969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60838346210558091584383669 5703594957239821086035969)
          ·
            refine ⟨4277696217929865814526977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5703594957239821086035969 4277696217929865814526977)
            ·
              refine ⟨3208272163447399360895233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4277696217929865814526977 3208272163447399360895233)
              ·
                refine ⟨2406204122585549520671425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3208272163447399360895233 2406204122585549520671425)
                ·
                  refine ⟨1804653091939162140503569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2406204122585549520671425 1804653091939162140503569)
                  ·
                    refine ⟨1353489818954371605377677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1804653091939162140503569 1353489818954371605377677)
                    ·
                      refine ⟨507558682107889352016629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1353489818954371605377677 507558682107889352016629)
                      ·
                        rfl

theorem cell23_988467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 2, 2, 3].length) (baseStart_988467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_988467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_988467 prefixEnd_988467 := by exact prefixLift 988467
  have htrace : WordTrace (prefixWord ++ tailWord_988467) baseStart_988467 baseEnd_988467 := by
    simpa [prefixWord, tailWord_988467, baseEnd_988467] using wordTrace_append hprefix tailTrace_988467
  have hstable : (prefixWord ++ tailWord_988467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988467).length < 2 ^ (prefixWord ++ tailWord_988467).sum := by decide
  have hdescent : baseEnd_988467 < baseStart_988467 := by decide
  rcases family_descends (prefixWord ++ tailWord_988467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988474 : List Nat := [3, 1, 1, 1, 4, 1, 3, 4, 1, 4]
def baseStart_988474 : Nat := 118140960795 + 988474 * 2 ^ 59
def prefixEnd_988474 : Nat := 4983230072969 + 3 ^ 40 * 988474 * 2
def baseEnd_988474 : Nat := 169187425490823608209699

theorem tailTrace_988474 : CollatzResearch.WordTrace tailWord_988474 prefixEnd_988474 169187425490823608209699 := by
  unfold tailWord_988474
  simp only [CollatzResearch.WordTrace]
  refine ⟨9013152155233747691007119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24035072413956660509352317 9013152155233747691007119)
  ·
    refine ⟨13519728232850621536510679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9013152155233747691007119 13519728232850621536510679)
    ·
      refine ⟨20279592349275932304766019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13519728232850621536510679 20279592349275932304766019)
      ·
        refine ⟨30419388523913898457149029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20279592349275932304766019 30419388523913898457149029)
        ·
          refine ⟨5703635348233855960715443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30419388523913898457149029 5703635348233855960715443)
          ·
            refine ⟨8555453022350783941073165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5703635348233855960715443 8555453022350783941073165)
            ·
              refine ⟨3208294883381543977902437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8555453022350783941073165 3208294883381543977902437)
              ·
                refine ⟨601555290634039495856707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3208294883381543977902437 601555290634039495856707)
                ·
                  refine ⟨902332935951059243785061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 601555290634039495856707 902332935951059243785061)
                  ·
                    refine ⟨169187425490823608209699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 902332935951059243785061 169187425490823608209699)
                    ·
                      rfl

theorem cell23_988474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 4, 1, 4].length) (baseStart_988474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_988474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_988474 prefixEnd_988474 := by exact prefixLift 988474
  have htrace : WordTrace (prefixWord ++ tailWord_988474) baseStart_988474 baseEnd_988474 := by
    simpa [prefixWord, tailWord_988474, baseEnd_988474] using wordTrace_append hprefix tailTrace_988474
  have hstable : (prefixWord ++ tailWord_988474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988474).length < 2 ^ (prefixWord ++ tailWord_988474).sum := by decide
  have hdescent : baseEnd_988474 < baseStart_988474 := by decide
  rcases family_descends (prefixWord ++ tailWord_988474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988514 : List Nat := [3, 3, 2, 1, 1, 1, 1, 2, 5, 1, 3]
def baseStart_988514 : Nat := 118140960795 + 988514 * 2 ^ 59
def prefixEnd_988514 : Nat := 4983230072969 + 3 ^ 40 * 988514 * 2
def baseEnd_988514 : Nat := 507582815698650668128913

theorem tailTrace_988514 : CollatzResearch.WordTrace tailWord_988514 prefixEnd_988514 507582815698650668128913 := by
  unfold tailWord_988514
  simp only [CollatzResearch.WordTrace]
  refine ⟨9013516885197519398871149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24036045027193385063656397 9013516885197519398871149)
  ·
    refine ⟨3380068831949069774576681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9013516885197519398871149 3380068831949069774576681)
    ·
      refine ⟨2535051623961802330932511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3380068831949069774576681 2535051623961802330932511)
      ·
        refine ⟨3802577435942703496398767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2535051623961802330932511 3802577435942703496398767)
        ·
          refine ⟨5703866153914055244598151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3802577435942703496398767 5703866153914055244598151)
          ·
            refine ⟨8555799230871082866897227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5703866153914055244598151 8555799230871082866897227)
            ·
              refine ⟨12833698846306624300345841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8555799230871082866897227 12833698846306624300345841)
              ·
                refine ⟨9625274134729968225259381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12833698846306624300345841 9625274134729968225259381)
                ·
                  refine ⟨902369450130934521118067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9625274134729968225259381 902369450130934521118067)
                  ·
                    refine ⟨1353554175196401781677101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 902369450130934521118067 1353554175196401781677101)
                    ·
                      refine ⟨507582815698650668128913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1353554175196401781677101 507582815698650668128913)
                      ·
                        rfl

theorem cell23_988514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_988514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_988514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_988514 prefixEnd_988514 := by exact prefixLift 988514
  have htrace : WordTrace (prefixWord ++ tailWord_988514) baseStart_988514 baseEnd_988514 := by
    simpa [prefixWord, tailWord_988514, baseEnd_988514] using wordTrace_append hprefix tailTrace_988514
  have hstable : (prefixWord ++ tailWord_988514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988514).length < 2 ^ (prefixWord ++ tailWord_988514).sum := by decide
  have hdescent : baseEnd_988514 < baseStart_988514 := by decide
  rcases family_descends (prefixWord ++ tailWord_988514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988517 : List Nat := [1, 3, 1, 3, 1, 2, 3, 3, 1, 5]
def baseStart_988517 : Nat := 118140960795 + 988517 * 2 ^ 59
def prefixEnd_988517 : Nat := 4983230072969 + 3 ^ 40 * 988517 * 2
def baseEnd_988517 : Nat := 169194785380204718797133

theorem tailTrace_988517 : CollatzResearch.WordTrace tailWord_988517 prefixEnd_988517 169194785380204718797133 := by
  unfold tailWord_988517
  simp only [CollatzResearch.WordTrace]
  refine ⟨36054176959779209107843805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24036117973186139405229203 36054176959779209107843805)
  ·
    refine ⟨13520316359917203415441427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36054176959779209107843805 13520316359917203415441427)
    ·
      refine ⟨20280474539875805123162141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13520316359917203415441427 20280474539875805123162141)
      ·
        refine ⟨7605177952453426921185803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20280474539875805123162141 7605177952453426921185803)
        ·
          refine ⟨11407766928680140381778705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7605177952453426921185803 11407766928680140381778705)
          ·
            refine ⟨8555825196510105286334029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11407766928680140381778705 8555825196510105286334029)
            ·
              refine ⟨3208434448691289482375261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8555825196510105286334029 3208434448691289482375261)
              ·
                refine ⟨1203162918259233555890723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3208434448691289482375261 1203162918259233555890723)
                ·
                  refine ⟨1804744377388850333836085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1203162918259233555890723 1804744377388850333836085)
                  ·
                    refine ⟨169194785380204718797133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1804744377388850333836085 169194785380204718797133)
                    ·
                      rfl

theorem cell23_988517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 3, 1, 5].length) (baseStart_988517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_988517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_988517 prefixEnd_988517 := by exact prefixLift 988517
  have htrace : WordTrace (prefixWord ++ tailWord_988517) baseStart_988517 baseEnd_988517 := by
    simpa [prefixWord, tailWord_988517, baseEnd_988517] using wordTrace_append hprefix tailTrace_988517
  have hstable : (prefixWord ++ tailWord_988517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988517).length < 2 ^ (prefixWord ++ tailWord_988517).sum := by decide
  have hdescent : baseEnd_988517 < baseStart_988517 := by decide
  rcases family_descends (prefixWord ++ tailWord_988517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988547 : List Nat := [1, 1, 1, 3, 5, 1, 3, 1, 1, 6]
def baseStart_988547 : Nat := 118140960795 + 988547 * 2 ^ 59
def prefixEnd_988547 : Nat := 4983230072969 + 3 ^ 40 * 988547 * 2
def baseEnd_988547 : Nat := 169199920186749679672087

theorem tailTrace_988547 : CollatzResearch.WordTrace tailWord_988547 prefixEnd_988547 169199920186749679672087 := by
  unfold tailWord_988547
  simp only [CollatzResearch.WordTrace]
  refine ⟨36055271149670524231435895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24036847433113682820957263 36055271149670524231435895)
  ·
    refine ⟨54082906724505786347153843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36055271149670524231435895 54082906724505786347153843)
    ·
      refine ⟨81124360086758679520730765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54082906724505786347153843 81124360086758679520730765)
      ·
        refine ⟨30421635032534504820274037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81124360086758679520730765 30421635032534504820274037)
        ·
          refine ⟨2852028284300109826900691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30421635032534504820274037 2852028284300109826900691)
          ·
            refine ⟨4278042426450164740351037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2852028284300109826900691 4278042426450164740351037)
            ·
              refine ⟨1604265909918811777631639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4278042426450164740351037 1604265909918811777631639)
              ·
                refine ⟨2406398864878217666447459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1604265909918811777631639 2406398864878217666447459)
                ·
                  refine ⟨3609598297317326499671189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2406398864878217666447459 3609598297317326499671189)
                  ·
                    refine ⟨169199920186749679672087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3609598297317326499671189 169199920186749679672087)
                    ·
                      rfl

theorem cell23_988547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 6].length) (baseStart_988547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_988547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_988547 prefixEnd_988547 := by exact prefixLift 988547
  have htrace : WordTrace (prefixWord ++ tailWord_988547) baseStart_988547 baseEnd_988547 := by
    simpa [prefixWord, tailWord_988547, baseEnd_988547] using wordTrace_append hprefix tailTrace_988547
  have hstable : (prefixWord ++ tailWord_988547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988547).length < 2 ^ (prefixWord ++ tailWord_988547).sum := by decide
  have hdescent : baseEnd_988547 < baseStart_988547 := by decide
  rcases family_descends (prefixWord ++ tailWord_988547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988564 : List Nat := [2, 4, 2, 1, 2, 1, 1, 2, 4, 4]
def baseStart_988564 : Nat := 118140960795 + 988564 * 2 ^ 59
def prefixEnd_988564 : Nat := 4983230072969 + 3 ^ 40 * 988564 * 2
def baseEnd_988564 : Nat := 169202829910458490834561

theorem tailTrace_988564 : CollatzResearch.WordTrace tailWord_988564 prefixEnd_988564 169202829910458490834561 := by
  unfold tailWord_988564
  simp only [CollatzResearch.WordTrace]
  refine ⟨18027945595304468067402373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24037260793739290756536497 18027945595304468067402373)
  ·
    refine ⟨3380239799119587762637945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18027945595304468067402373 3380239799119587762637945)
    ·
      refine ⟨2535179849339690821978459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3380239799119587762637945 2535179849339690821978459)
      ·
        refine ⟨3802769774009536232967689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2535179849339690821978459 3802769774009536232967689)
        ·
          refine ⟨2852077330507152174725767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3802769774009536232967689 2852077330507152174725767)
          ·
            refine ⟨4278115995760728262088651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2852077330507152174725767 4278115995760728262088651)
            ·
              refine ⟨6417173993641092393132977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4278115995760728262088651 6417173993641092393132977)
              ·
                refine ⟨4812880495230819294849733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6417173993641092393132977 4812880495230819294849733)
                ·
                  refine ⟨902415092855778617784325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4812880495230819294849733 902415092855778617784325)
                  ·
                    refine ⟨169202829910458490834561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 902415092855778617784325 169202829910458490834561)
                    ·
                      rfl

theorem cell23_988564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_988564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_988564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_988564 prefixEnd_988564 := by exact prefixLift 988564
  have htrace : WordTrace (prefixWord ++ tailWord_988564) baseStart_988564 baseEnd_988564 := by
    simpa [prefixWord, tailWord_988564, baseEnd_988564] using wordTrace_append hprefix tailTrace_988564
  have hstable : (prefixWord ++ tailWord_988564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988564).length < 2 ^ (prefixWord ++ tailWord_988564).sum := by decide
  have hdescent : baseEnd_988564 < baseStart_988564 := by decide
  rcases family_descends (prefixWord ++ tailWord_988564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988657 : List Nat := [1, 2, 2, 2, 3, 2, 1, 1, 1, 4, 4]
def baseStart_988657 : Nat := 118140960795 + 988657 * 2 ^ 59
def prefixEnd_988657 : Nat := 4983230072969 + 3 ^ 40 * 988657 * 2
def baseEnd_988657 : Nat := 507656243432243608640755

theorem tailTrace_988657 : CollatzResearch.WordTrace tailWord_988657 prefixEnd_988657 507656243432243608640755 := by
  unfold tailWord_988657
  simp only [CollatzResearch.WordTrace]
  refine ⟨36059283179272013017940225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24039522119514675345293483 36059283179272013017940225)
  ·
    refine ⟨27044462384454009763455169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36059283179272013017940225 27044462384454009763455169)
    ·
      refine ⟨20283346788340507322591377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27044462384454009763455169 20283346788340507322591377)
      ·
        refine ⟨15212510091255380491943533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20283346788340507322591377 15212510091255380491943533)
        ·
          refine ⟨5704691284220767684478825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15212510091255380491943533 5704691284220767684478825)
          ·
            refine ⟨4278518463165575763359119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5704691284220767684478825 4278518463165575763359119)
            ·
              refine ⟨6417777694748363645038679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4278518463165575763359119 6417777694748363645038679)
              ·
                refine ⟨9626666542122545467558019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6417777694748363645038679 9626666542122545467558019)
                ·
                  refine ⟨14439999813183818201337029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9626666542122545467558019 14439999813183818201337029)
                  ·
                    refine ⟨2707499964971965912750693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14439999813183818201337029 2707499964971965912750693)
                    ·
                      refine ⟨507656243432243608640755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2707499964971965912750693 507656243432243608640755)
                      ·
                        rfl

theorem cell23_988657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_988657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_988657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_988657 prefixEnd_988657 := by exact prefixLift 988657
  have htrace : WordTrace (prefixWord ++ tailWord_988657) baseStart_988657 baseEnd_988657 := by
    simpa [prefixWord, tailWord_988657, baseEnd_988657] using wordTrace_append hprefix tailTrace_988657
  have hstable : (prefixWord ++ tailWord_988657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988657).length < 2 ^ (prefixWord ++ tailWord_988657).sum := by decide
  have hdescent : baseEnd_988657 < baseStart_988657 := by decide
  rcases family_descends (prefixWord ++ tailWord_988657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988677 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 3, 5, 3]
def baseStart_988677 : Nat := 118140960795 + 988677 * 2 ^ 59
def prefixEnd_988677 : Nat := 4983230072969 + 3 ^ 40 * 988677 * 2
def baseEnd_988677 : Nat := 507666513045333530390663

theorem tailTrace_988677 : CollatzResearch.WordTrace tailWord_988677 prefixEnd_988677 507666513045333530390663 := by
  unfold tailWord_988677
  simp only [CollatzResearch.WordTrace]
  refine ⟨36060012639199556433668285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24040008426133037622445523 36060012639199556433668285)
  ·
    refine ⟨13522504739699833662625607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36060012639199556433668285 13522504739699833662625607)
    ·
      refine ⟨20283757109549750493938411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13522504739699833662625607 20283757109549750493938411)
      ·
        refine ⟨30425635664324625740907617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20283757109549750493938411 30425635664324625740907617)
        ·
          refine ⟨22819226748243469305680713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30425635664324625740907617 22819226748243469305680713)
          ·
            refine ⟨17114420061182601979260535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22819226748243469305680713 17114420061182601979260535)
            ·
              refine ⟨25671630091773902968890803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17114420061182601979260535 25671630091773902968890803)
              ·
                refine ⟨38507445137660854453336205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25671630091773902968890803 38507445137660854453336205)
                ·
                  refine ⟨14440291926622820420001077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38507445137660854453336205 14440291926622820420001077)
                  ·
                    refine ⟨1353777368120889414375101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14440291926622820420001077 1353777368120889414375101)
                    ·
                      refine ⟨507666513045333530390663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1353777368120889414375101 507666513045333530390663)
                      ·
                        rfl

theorem cell23_988677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 5, 3].length) (baseStart_988677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_988677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_988677 prefixEnd_988677 := by exact prefixLift 988677
  have htrace : WordTrace (prefixWord ++ tailWord_988677) baseStart_988677 baseEnd_988677 := by
    simpa [prefixWord, tailWord_988677, baseEnd_988677] using wordTrace_append hprefix tailTrace_988677
  have hstable : (prefixWord ++ tailWord_988677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988677).length < 2 ^ (prefixWord ++ tailWord_988677).sum := by decide
  have hdescent : baseEnd_988677 < baseStart_988677 := by decide
  rcases family_descends (prefixWord ++ tailWord_988677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988712 : List Nat := [2, 1, 5, 2, 2, 1, 3, 1, 2, 2, 2]
def baseStart_988712 : Nat := 118140960795 + 988712 * 2 ^ 59
def prefixEnd_988712 : Nat := 4983230072969 + 3 ^ 40 * 988712 * 2
def baseEnd_988712 : Nat := 507684484868240893453003

theorem tailTrace_988712 : CollatzResearch.WordTrace tailWord_988712 prefixEnd_988712 507684484868240893453003 := by
  unfold tailWord_988712
  simp only [CollatzResearch.WordTrace]
  refine ⟨18030644597036378705596195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24040859462715171607461593 18030644597036378705596195)
  ·
    refine ⟨27045966895554568058394293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18030644597036378705596195 27045966895554568058394293)
    ·
      refine ⟨2535559396458240755474465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27045966895554568058394293 2535559396458240755474465)
      ·
        refine ⟨1901669547343680566605849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2535559396458240755474465 1901669547343680566605849)
        ·
          refine ⟨1426252160507760424954387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1901669547343680566605849 1426252160507760424954387)
          ·
            refine ⟨2139378240761640637431581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1426252160507760424954387 2139378240761640637431581)
            ·
              refine ⟨802266840285615239036843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2139378240761640637431581 802266840285615239036843)
              ·
                refine ⟨1203400260428422858555265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 802266840285615239036843 1203400260428422858555265)
                ·
                  refine ⟨902550195321317143916449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1203400260428422858555265 902550195321317143916449)
                  ·
                    refine ⟨676912646490987857937337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 902550195321317143916449 676912646490987857937337)
                    ·
                      refine ⟨507684484868240893453003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 676912646490987857937337 507684484868240893453003)
                      ·
                        rfl

theorem cell23_988712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_988712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_988712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_988712 prefixEnd_988712 := by exact prefixLift 988712
  have htrace : WordTrace (prefixWord ++ tailWord_988712) baseStart_988712 baseEnd_988712 := by
    simpa [prefixWord, tailWord_988712, baseEnd_988712] using wordTrace_append hprefix tailTrace_988712
  have hstable : (prefixWord ++ tailWord_988712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988712).length < 2 ^ (prefixWord ++ tailWord_988712).sum := by decide
  have hdescent : baseEnd_988712 < baseStart_988712 := by decide
  rcases family_descends (prefixWord ++ tailWord_988712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988761 : List Nat := [1, 2, 1, 2, 2, 1, 1, 8, 1, 4]
def baseStart_988761 : Nat := 118140960795 + 988761 * 2 ^ 59
def prefixEnd_988761 : Nat := 4983230072969 + 3 ^ 40 * 988761 * 2
def baseEnd_988761 : Nat := 169236548473437067246759

theorem tailTrace_988761 : CollatzResearch.WordTrace tailWord_988761 prefixEnd_988761 169236548473437067246759 := by
  unfold tailWord_988761
  simp only [CollatzResearch.WordTrace]
  refine ⟨36063076370895238779726137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24042050913930159186484091 36063076370895238779726137)
  ·
    refine ⟨27047307278171429084794603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36063076370895238779726137 27047307278171429084794603)
    ·
      refine ⟨40570960917257143627191905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27047307278171429084794603 40570960917257143627191905)
      ·
        refine ⟨30428220687942857720393929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40570960917257143627191905 30428220687942857720393929)
        ·
          refine ⟨22821165515957143290295447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30428220687942857720393929 22821165515957143290295447)
          ·
            refine ⟨34231748273935714935443171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22821165515957143290295447 34231748273935714935443171)
            ·
              refine ⟨51347622410903572403164757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34231748273935714935443171 51347622410903572403164757)
              ·
                refine ⟨601729950127776239099587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 51347622410903572403164757 601729950127776239099587)
                ·
                  refine ⟨902594925191664358649381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 601729950127776239099587 902594925191664358649381)
                  ·
                    refine ⟨169236548473437067246759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 902594925191664358649381 169236548473437067246759)
                    ·
                      rfl

theorem cell23_988761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 8, 1, 4].length) (baseStart_988761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_988761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_988761 prefixEnd_988761 := by exact prefixLift 988761
  have htrace : WordTrace (prefixWord ++ tailWord_988761) baseStart_988761 baseEnd_988761 := by
    simpa [prefixWord, tailWord_988761, baseEnd_988761] using wordTrace_append hprefix tailTrace_988761
  have hstable : (prefixWord ++ tailWord_988761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988761).length < 2 ^ (prefixWord ++ tailWord_988761).sum := by decide
  have hdescent : baseEnd_988761 < baseStart_988761 := by decide
  rcases family_descends (prefixWord ++ tailWord_988761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988777 : List Nat := [1, 2, 1, 1, 1, 4, 2, 2, 1, 2, 6]
def baseStart_988777 : Nat := 118140960795 + 988777 * 2 ^ 59
def prefixEnd_988777 : Nat := 4983230072969 + 3 ^ 40 * 988777 * 2
def baseEnd_988777 : Nat := 507717861110783139140203

theorem tailTrace_988777 : CollatzResearch.WordTrace tailWord_988777 prefixEnd_988777 507717861110783139140203 := by
  unfold tailWord_988777
  simp only [CollatzResearch.WordTrace]
  refine ⟨36063659938837273512308585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24042439959224849008205723 36063659938837273512308585)
  ·
    refine ⟨27047744954127955134231439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36063659938837273512308585 27047744954127955134231439)
    ·
      refine ⟨40571617431191932701347159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27047744954127955134231439 40571617431191932701347159)
      ·
        refine ⟨60857426146787899052020739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40571617431191932701347159 60857426146787899052020739)
        ·
          refine ⟨91286139220181848578031109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60857426146787899052020739 91286139220181848578031109)
          ·
            refine ⟨17116151103784096608380833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91286139220181848578031109 17116151103784096608380833)
            ·
              refine ⟨12837113327838072456285625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17116151103784096608380833 12837113327838072456285625)
              ·
                refine ⟨9627834995878554342214219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12837113327838072456285625 9627834995878554342214219)
                ·
                  refine ⟨14441752493817831513321329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9627834995878554342214219 14441752493817831513321329)
                  ·
                    refine ⟨10831314370363373634990997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14441752493817831513321329 10831314370363373634990997)
                    ·
                      refine ⟨507717861110783139140203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10831314370363373634990997 507717861110783139140203)
                      ·
                        rfl

theorem cell23_988777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 2, 6].length) (baseStart_988777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_988777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_988777 prefixEnd_988777 := by exact prefixLift 988777
  have htrace : WordTrace (prefixWord ++ tailWord_988777) baseStart_988777 baseEnd_988777 := by
    simpa [prefixWord, tailWord_988777, baseEnd_988777] using wordTrace_append hprefix tailTrace_988777
  have hstable : (prefixWord ++ tailWord_988777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988777).length < 2 ^ (prefixWord ++ tailWord_988777).sum := by decide
  have hdescent : baseEnd_988777 < baseStart_988777 := by decide
  rcases family_descends (prefixWord ++ tailWord_988777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988808 : List Nat := [2, 1, 3, 5, 1, 1, 2, 2, 6]
def baseStart_988808 : Nat := 118140960795 + 988808 * 2 ^ 59
def prefixEnd_988808 : Nat := 4983230072969 + 3 ^ 40 * 988808 * 2
def baseEnd_988808 : Nat := 56414864334563613094729

theorem tailTrace_988808 : CollatzResearch.WordTrace tailWord_988808 prefixEnd_988808 56414864334563613094729 := by
  unfold tailWord_988808
  simp only [CollatzResearch.WordTrace]
  refine ⟨18032395300862482903343539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24043193734483310537791385 18032395300862482903343539)
  ·
    refine ⟨27048592951293724355015309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18032395300862482903343539 27048592951293724355015309)
    ·
      refine ⟨10143222356735146633130741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27048592951293724355015309 10143222356735146633130741)
      ·
        refine ⟨950927095943919996856007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10143222356735146633130741 950927095943919996856007)
        ·
          refine ⟨1426390643915879995284011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 950927095943919996856007 1426390643915879995284011)
          ·
            refine ⟨2139585965873819992926017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1426390643915879995284011 2139585965873819992926017)
            ·
              refine ⟨1604689474405364994694513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2139585965873819992926017 1604689474405364994694513)
              ·
                refine ⟨1203517105804023746020885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1604689474405364994694513 1203517105804023746020885)
                ·
                  refine ⟨56414864334563613094729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1203517105804023746020885 56414864334563613094729)
                  ·
                    rfl

theorem cell23_988808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 2, 6].length) (baseStart_988808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_988808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_988808 prefixEnd_988808 := by exact prefixLift 988808
  have htrace : WordTrace (prefixWord ++ tailWord_988808) baseStart_988808 baseEnd_988808 := by
    simpa [prefixWord, tailWord_988808, baseEnd_988808] using wordTrace_append hprefix tailTrace_988808
  have hstable : (prefixWord ++ tailWord_988808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988808).length < 2 ^ (prefixWord ++ tailWord_988808).sum := by decide
  have hdescent : baseEnd_988808 < baseStart_988808 := by decide
  rcases family_descends (prefixWord ++ tailWord_988808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988811 : List Nat := [1, 1, 1, 1, 4, 1, 3, 4, 2, 3, 2]
def baseStart_988811 : Nat := 118140960795 + 988811 * 2 ^ 59
def prefixEnd_988811 : Nat := 4983230072969 + 3 ^ 40 * 988811 * 2
def baseEnd_988811 : Nat := 507735319453036006115047

theorem tailTrace_988811 : CollatzResearch.WordTrace tailWord_988811 prefixEnd_988811 507735319453036006115047 := by
  unfold tailWord_988811
  simp only [CollatzResearch.WordTrace]
  refine ⟨36064900020714097319046287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24043266680476064879364191 36064900020714097319046287)
  ·
    refine ⟨54097350031071145978569431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36064900020714097319046287 54097350031071145978569431)
    ·
      refine ⟨81146025046606718967854147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54097350031071145978569431 81146025046606718967854147)
      ·
        refine ⟨121719037569910078451781221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81146025046606718967854147 121719037569910078451781221)
        ·
          refine ⟨22822319544358139709708979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121719037569910078451781221 22822319544358139709708979)
          ·
            refine ⟨34233479316537209564563469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22822319544358139709708979 34233479316537209564563469)
            ·
              refine ⟨12837554743701453586711301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34233479316537209564563469 12837554743701453586711301)
              ·
                refine ⟨2407041514444022547508369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12837554743701453586711301 2407041514444022547508369)
                ·
                  refine ⟨1805281135833016910631277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2407041514444022547508369 1805281135833016910631277)
                  ·
                    refine ⟨676980425937381341486729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1805281135833016910631277 676980425937381341486729)
                    ·
                      refine ⟨507735319453036006115047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 676980425937381341486729 507735319453036006115047)
                      ·
                        rfl

theorem cell23_988811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 2, 3, 2].length) (baseStart_988811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_988811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_988811 prefixEnd_988811 := by exact prefixLift 988811
  have htrace : WordTrace (prefixWord ++ tailWord_988811) baseStart_988811 baseEnd_988811 := by
    simpa [prefixWord, tailWord_988811, baseEnd_988811] using wordTrace_append hprefix tailTrace_988811
  have hstable : (prefixWord ++ tailWord_988811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988811).length < 2 ^ (prefixWord ++ tailWord_988811).sum := by decide
  have hdescent : baseEnd_988811 < baseStart_988811 := by decide
  rcases family_descends (prefixWord ++ tailWord_988811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988858 : List Nat := [3, 1, 1, 1, 2, 4, 4, 1, 1, 1, 4]
def baseStart_988858 : Nat := 118140960795 + 988858 * 2 ^ 59
def prefixEnd_988858 : Nat := 4983230072969 + 3 ^ 40 * 988858 * 2
def baseEnd_988858 : Nat := 507759453043797322227331

theorem tailTrace_988858 : CollatzResearch.WordTrace tailWord_988858 prefixEnd_988858 507759453043797322227331 := by
  unfold tailWord_988858
  simp only [CollatzResearch.WordTrace]
  refine ⟨9016653562885956086501807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24044409501029216230671485 9016653562885956086501807)
  ·
    refine ⟨13524980344328934129752711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9016653562885956086501807 13524980344328934129752711)
    ·
      refine ⟨20287470516493401194629067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13524980344328934129752711 20287470516493401194629067)
      ·
        refine ⟨30431205774740101791943601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20287470516493401194629067 30431205774740101791943601)
        ·
          refine ⟨22823404331055076343957701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30431205774740101791943601 22823404331055076343957701)
          ·
            refine ⟨4279388312072826814492069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22823404331055076343957701 4279388312072826814492069)
            ·
              refine ⟨802385308513655027717263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4279388312072826814492069 802385308513655027717263)
              ·
                refine ⟨1203577962770482541575895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 802385308513655027717263 1203577962770482541575895)
                ·
                  refine ⟨1805366944155723812363843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1203577962770482541575895 1805366944155723812363843)
                  ·
                    refine ⟨2708050416233585718545765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1805366944155723812363843 2708050416233585718545765)
                    ·
                      refine ⟨507759453043797322227331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2708050416233585718545765 507759453043797322227331)
                      ·
                        rfl

theorem cell23_988858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 1, 1, 1, 4].length) (baseStart_988858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_988858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_988858 prefixEnd_988858 := by exact prefixLift 988858
  have htrace : WordTrace (prefixWord ++ tailWord_988858) baseStart_988858 baseEnd_988858 := by
    simpa [prefixWord, tailWord_988858, baseEnd_988858] using wordTrace_append hprefix tailTrace_988858
  have hstable : (prefixWord ++ tailWord_988858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988858).length < 2 ^ (prefixWord ++ tailWord_988858).sum := by decide
  have hdescent : baseEnd_988858 < baseStart_988858 := by decide
  rcases family_descends (prefixWord ++ tailWord_988858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988909 : List Nat := [1, 5, 1, 2, 1, 4, 1, 3, 1, 2, 2]
def baseStart_988909 : Nat := 118140960795 + 988909 * 2 ^ 59
def prefixEnd_988909 : Nat := 4983230072969 + 3 ^ 40 * 988909 * 2
def baseEnd_988909 : Nat := 507785640557176622689597

theorem tailTrace_988909 : CollatzResearch.WordTrace tailWord_988909 prefixEnd_988909 507785640557176622689597 := by
  unfold tailWord_988909
  simp only [CollatzResearch.WordTrace]
  refine ⟨36068474374359060056113781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24045649582906040037409187 36068474374359060056113781)
  ·
    refine ⟨3381419472596161880260667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36068474374359060056113781 3381419472596161880260667)
    ·
      refine ⟨5072129208894242820391001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3381419472596161880260667 5072129208894242820391001)
      ·
        refine ⟨3804096906670682115293251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5072129208894242820391001 3804096906670682115293251)
        ·
          refine ⟨5706145360006023172939877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3804096906670682115293251 5706145360006023172939877)
          ·
            refine ⟨1069902255001129344926227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5706145360006023172939877 1069902255001129344926227)
            ·
              refine ⟨1604853382501694017389341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1069902255001129344926227 1604853382501694017389341)
              ·
                refine ⟨601820018438135256521003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1604853382501694017389341 601820018438135256521003)
                ·
                  refine ⟨902730027657202884781505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 601820018438135256521003 902730027657202884781505)
                  ·
                    refine ⟨677047520742902163586129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 902730027657202884781505 677047520742902163586129)
                    ·
                      refine ⟨507785640557176622689597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 677047520742902163586129 507785640557176622689597)
                      ·
                        rfl

theorem cell23_988909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_988909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_988909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_988909 prefixEnd_988909 := by exact prefixLift 988909
  have htrace : WordTrace (prefixWord ++ tailWord_988909) baseStart_988909 baseEnd_988909 := by
    simpa [prefixWord, tailWord_988909, baseEnd_988909] using wordTrace_append hprefix tailTrace_988909
  have hstable : (prefixWord ++ tailWord_988909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988909).length < 2 ^ (prefixWord ++ tailWord_988909).sum := by decide
  have hdescent : baseEnd_988909 < baseStart_988909 := by decide
  rcases family_descends (prefixWord ++ tailWord_988909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988926 : List Nat := [4, 2, 2, 1, 3, 1, 3, 2, 1, 2, 2]
def baseStart_988926 : Nat := 118140960795 + 988926 * 2 ^ 59
def prefixEnd_988926 : Nat := 4983230072969 + 3 ^ 40 * 988926 * 2
def baseEnd_988926 : Nat := 507794369728303056177019

theorem tailTrace_988926 : CollatzResearch.WordTrace tailWord_988926 prefixEnd_988926 507794369728303056177019 := by
  unfold tailWord_988926
  simp only [CollatzResearch.WordTrace]
  refine ⟨4508636801912183994935329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24046062943531647972988421 4508636801912183994935329)
  ·
    refine ⟨3381477601434137996201497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4508636801912183994935329 3381477601434137996201497)
    ·
      refine ⟨2536108201075603497151123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3381477601434137996201497 2536108201075603497151123)
      ·
        refine ⟨3804162301613405245726685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2536108201075603497151123 3804162301613405245726685)
        ·
          refine ⟨1426560863105026967147507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3804162301613405245726685 1426560863105026967147507)
          ·
            refine ⟨2139841294657540450721261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1426560863105026967147507 2139841294657540450721261)
            ·
              refine ⟨802440485496577669020473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2139841294657540450721261 802440485496577669020473)
              ·
                refine ⟨601830364122433251765355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 802440485496577669020473 601830364122433251765355)
                ·
                  refine ⟨902745546183649877648033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 601830364122433251765355 902745546183649877648033)
                  ·
                    refine ⟨677059159637737408236025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 902745546183649877648033 677059159637737408236025)
                    ·
                      refine ⟨507794369728303056177019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 677059159637737408236025 507794369728303056177019)
                      ·
                        rfl

theorem cell23_988926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_988926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_988926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_988926 prefixEnd_988926 := by exact prefixLift 988926
  have htrace : WordTrace (prefixWord ++ tailWord_988926) baseStart_988926 baseEnd_988926 := by
    simpa [prefixWord, tailWord_988926, baseEnd_988926] using wordTrace_append hprefix tailTrace_988926
  have hstable : (prefixWord ++ tailWord_988926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988926).length < 2 ^ (prefixWord ++ tailWord_988926).sum := by decide
  have hdescent : baseEnd_988926 < baseStart_988926 := by decide
  rcases family_descends (prefixWord ++ tailWord_988926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988951 : List Nat := [1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 5]
def baseStart_988951 : Nat := 118140960795 + 988951 * 2 ^ 59
def prefixEnd_988951 : Nat := 4983230072969 + 3 ^ 40 * 988951 * 2
def baseEnd_988951 : Nat := 507807206744665458364403

theorem tailTrace_988951 : CollatzResearch.WordTrace tailWord_988951 prefixEnd_988951 507807206744665458364403 := by
  unfold tailWord_988951
  simp only [CollatzResearch.WordTrace]
  refine ⟨36070006240206901229142707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24046670826804600819428471 36070006240206901229142707)
  ·
    refine ⟨54105009360310351843714061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36070006240206901229142707 54105009360310351843714061)
    ·
      refine ⟨20289378510116381941392773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54105009360310351843714061 20289378510116381941392773)
      ·
        refine ⟨3804258470646821614011145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20289378510116381941392773 3804258470646821614011145)
        ·
          refine ⟨2853193852985116210508359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3804258470646821614011145 2853193852985116210508359)
          ·
            refine ⟨4279790779477674315762539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2853193852985116210508359 4279790779477674315762539)
            ·
              refine ⟨6419686169216511473643809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4279790779477674315762539 6419686169216511473643809)
              ·
                refine ⟨4814764626912383605232857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6419686169216511473643809 4814764626912383605232857)
                ·
                  refine ⟨3611073470184287703924643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4814764626912383605232857 3611073470184287703924643)
                  ·
                    refine ⟨5416610205276431555886965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3611073470184287703924643 5416610205276431555886965)
                    ·
                      refine ⟨507807206744665458364403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5416610205276431555886965 507807206744665458364403)
                      ·
                        rfl

theorem cell23_988951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_988951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_988951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_988951 prefixEnd_988951 := by exact prefixLift 988951
  have htrace : WordTrace (prefixWord ++ tailWord_988951) baseStart_988951 baseEnd_988951 := by
    simpa [prefixWord, tailWord_988951, baseEnd_988951] using wordTrace_append hprefix tailTrace_988951
  have hstable : (prefixWord ++ tailWord_988951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988951).length < 2 ^ (prefixWord ++ tailWord_988951).sum := by decide
  have hdescent : baseEnd_988951 < baseStart_988951 := by decide
  rcases family_descends (prefixWord ++ tailWord_988951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989082 : List Nat := [3, 1, 1, 4, 2, 1, 3, 3, 1, 4]
def baseStart_989082 : Nat := 118140960795 + 989082 * 2 ^ 59
def prefixEnd_989082 : Nat := 4983230072969 + 3 ^ 40 * 989082 * 2
def baseEnd_989082 : Nat := 169291490903468148608767

theorem tailTrace_989082 : CollatzResearch.WordTrace tailWord_989082 prefixEnd_989082 169291490903468148608767 := by
  unfold tailWord_989082
  simp only [CollatzResearch.WordTrace]
  refine ⟨9018696050683077650540375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24049856135154873734774333 9018696050683077650540375)
  ·
    refine ⟨13528044076024616475810563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9018696050683077650540375 13528044076024616475810563)
    ·
      refine ⟨20292066114036924713715845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13528044076024616475810563 20292066114036924713715845)
      ·
        refine ⟨3804762396381923383821721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20292066114036924713715845 3804762396381923383821721)
        ·
          refine ⟨2853571797286442537866291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3804762396381923383821721 2853571797286442537866291)
          ·
            refine ⟨4280357695929663806799437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2853571797286442537866291 4280357695929663806799437)
            ·
              refine ⟨1605134135973623927549789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4280357695929663806799437 1605134135973623927549789)
              ·
                refine ⟨601925300990108972831171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1605134135973623927549789 601925300990108972831171)
                ·
                  refine ⟨902887951485163459246757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 601925300990108972831171 902887951485163459246757)
                  ·
                    refine ⟨169291490903468148608767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 902887951485163459246757 169291490903468148608767)
                    ·
                      rfl

theorem cell23_989082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 3, 1, 4].length) (baseStart_989082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989082 prefixEnd_989082 := by exact prefixLift 989082
  have htrace : WordTrace (prefixWord ++ tailWord_989082) baseStart_989082 baseEnd_989082 := by
    simpa [prefixWord, tailWord_989082, baseEnd_989082] using wordTrace_append hprefix tailTrace_989082
  have hstable : (prefixWord ++ tailWord_989082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989082).length < 2 ^ (prefixWord ++ tailWord_989082).sum := by decide
  have hdescent : baseEnd_989082 < baseStart_989082 := by decide
  rcases family_descends (prefixWord ++ tailWord_989082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989091 : List Nat := [1, 1, 1, 4, 1, 2, 1, 2, 5, 5]
def baseStart_989091 : Nat := 118140960795 + 989091 * 2 ^ 59
def prefixEnd_989091 : Nat := 4983230072969 + 3 ^ 40 * 989091 * 2
def baseEnd_989091 : Nat := 169293031345431636871253

theorem tailTrace_989091 : CollatzResearch.WordTrace tailWord_989091 prefixEnd_989091 169293031345431636871253 := by
  unfold tailWord_989091
  simp only [CollatzResearch.WordTrace]
  refine ⟨36075112459699705139239127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24050074973133136759492751 36075112459699705139239127)
  ·
    refine ⟨54112668689549557708858691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36075112459699705139239127 54112668689549557708858691)
    ·
      refine ⟨81169003034324336563288037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54112668689549557708858691 81169003034324336563288037)
      ·
        refine ⟨15219188068935813105616507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81169003034324336563288037 15219188068935813105616507)
        ·
          refine ⟨22828782103403719658424761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15219188068935813105616507 22828782103403719658424761)
          ·
            refine ⟨17121586577552789743818571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22828782103403719658424761 17121586577552789743818571)
            ·
              refine ⟨25682379866329184615727857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17121586577552789743818571 25682379866329184615727857)
              ·
                refine ⟨19261784899746888461795893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25682379866329184615727857 19261784899746888461795893)
                ·
                  refine ⟨1805792334351270793293365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19261784899746888461795893 1805792334351270793293365)
                  ·
                    refine ⟨169293031345431636871253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1805792334351270793293365 169293031345431636871253)
                    ·
                      rfl

theorem cell23_989091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 5, 5].length) (baseStart_989091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989091 prefixEnd_989091 := by exact prefixLift 989091
  have htrace : WordTrace (prefixWord ++ tailWord_989091) baseStart_989091 baseEnd_989091 := by
    simpa [prefixWord, tailWord_989091, baseEnd_989091] using wordTrace_append hprefix tailTrace_989091
  have hstable : (prefixWord ++ tailWord_989091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989091).length < 2 ^ (prefixWord ++ tailWord_989091).sum := by decide
  have hdescent : baseEnd_989091 < baseStart_989091 := by decide
  rcases family_descends (prefixWord ++ tailWord_989091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989111 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 2, 5, 4]
def baseStart_989111 : Nat := 118140960795 + 989111 * 2 ^ 59
def prefixEnd_989111 : Nat := 4983230072969 + 3 ^ 40 * 989111 * 2
def baseEnd_989111 : Nat := 507889363649384832363667

theorem tailTrace_989111 : CollatzResearch.WordTrace tailWord_989111 prefixEnd_989111 507889363649384832363667 := by
  unfold tailWord_989111
  simp only [CollatzResearch.WordTrace]
  refine ⟨36075841919627248554967187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24050561279751499036644791 36075841919627248554967187)
  ·
    refine ⟨54113762879440872832450781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36075841919627248554967187 54113762879440872832450781)
    ·
      refine ⟨20292661079790327312169043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54113762879440872832450781 20292661079790327312169043)
      ·
        refine ⟨30438991619685490968253565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20292661079790327312169043 30438991619685490968253565)
        ·
          refine ⟨11414621857382059113095087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30438991619685490968253565 11414621857382059113095087)
          ·
            refine ⟨17121932786073088669642631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11414621857382059113095087 17121932786073088669642631)
            ·
              refine ⟨25682899179109633004463947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17121932786073088669642631 25682899179109633004463947)
              ·
                refine ⟨38524348768664449506695921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25682899179109633004463947 38524348768664449506695921)
                ·
                  refine ⟨28893261576498337130021941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38524348768664449506695921 28893261576498337130021941)
                  ·
                    refine ⟨2708743272796719105939557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28893261576498337130021941 2708743272796719105939557)
                    ·
                      refine ⟨507889363649384832363667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2708743272796719105939557 507889363649384832363667)
                      ·
                        rfl

theorem cell23_989111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 5, 4].length) (baseStart_989111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989111 prefixEnd_989111 := by exact prefixLift 989111
  have htrace : WordTrace (prefixWord ++ tailWord_989111) baseStart_989111 baseEnd_989111 := by
    simpa [prefixWord, tailWord_989111, baseEnd_989111] using wordTrace_append hprefix tailTrace_989111
  have hstable : (prefixWord ++ tailWord_989111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989111).length < 2 ^ (prefixWord ++ tailWord_989111).sum := by decide
  have hdescent : baseEnd_989111 < baseStart_989111 := by decide
  rcases family_descends (prefixWord ++ tailWord_989111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989132 : List Nat := [2, 2, 1, 4, 1, 3, 2, 1, 2, 3, 2]
def baseStart_989132 : Nat := 118140960795 + 989132 * 2 ^ 59
def prefixEnd_989132 : Nat := 4983230072969 + 3 ^ 40 * 989132 * 2
def baseEnd_989132 : Nat := 507900146743129250201071

theorem tailTrace_989132 : CollatzResearch.WordTrace tailWord_989132 prefixEnd_989132 507900146743129250201071 := by
  unfold tailWord_989132
  simp only [CollatzResearch.WordTrace]
  refine ⟨18038303926275584570740825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24051071901700779427654433 18038303926275584570740825)
  ·
    refine ⟨13528727944706688428055619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18038303926275584570740825 13528727944706688428055619)
    ·
      refine ⟨20293091917060032642083429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13528727944706688428055619 20293091917060032642083429)
      ·
        refine ⟨3804954734448756120390643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20293091917060032642083429 3804954734448756120390643)
        ·
          refine ⟨5707432101673134180585965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3804954734448756120390643 5707432101673134180585965)
          ·
            refine ⟨2140287038127425317719737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5707432101673134180585965 2140287038127425317719737)
            ·
              refine ⟨1605215278595568988289803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2140287038127425317719737 1605215278595568988289803)
              ·
                refine ⟨2407822917893353482434705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1605215278595568988289803 2407822917893353482434705)
                ·
                  refine ⟨1805867188420015111826029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2407822917893353482434705 1805867188420015111826029)
                  ·
                    refine ⟨677200195657505666934761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1805867188420015111826029 677200195657505666934761)
                    ·
                      refine ⟨507900146743129250201071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 677200195657505666934761 507900146743129250201071)
                      ·
                        rfl

theorem cell23_989132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_989132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989132 prefixEnd_989132 := by exact prefixLift 989132
  have htrace : WordTrace (prefixWord ++ tailWord_989132) baseStart_989132 baseEnd_989132 := by
    simpa [prefixWord, tailWord_989132, baseEnd_989132] using wordTrace_append hprefix tailTrace_989132
  have hstable : (prefixWord ++ tailWord_989132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989132).length < 2 ^ (prefixWord ++ tailWord_989132).sum := by decide
  have hdescent : baseEnd_989132 < baseStart_989132 := by decide
  rcases family_descends (prefixWord ++ tailWord_989132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989151 : List Nat := [1, 1, 2, 3, 4, 12]
def baseStart_989151 : Nat := 118140960795 + 989151 * 2 ^ 59
def prefixEnd_989151 : Nat := 4983230072969 + 3 ^ 40 * 989151 * 2
def baseEnd_989151 : Nat := 2090164209364463686681

theorem tailTrace_989151 : CollatzResearch.WordTrace tailWord_989151 prefixEnd_989151 2090164209364463686681 := by
  unfold tailWord_989151
  simp only [CollatzResearch.WordTrace]
  refine ⟨36077300839482335386423307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24051533892988223590948871 36077300839482335386423307)
  ·
    refine ⟨54115951259223503079634961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36077300839482335386423307 54115951259223503079634961)
    ·
      refine ⟨40586963444417627309726221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54115951259223503079634961 40586963444417627309726221)
      ·
        refine ⟨15220111291656610241147333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40586963444417627309726221 15220111291656610241147333)
        ·
          refine ⟨2853770867185614420215125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15220111291656610241147333 2853770867185614420215125)
          ·
            refine ⟨2090164209364463686681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 2853770867185614420215125 2090164209364463686681)
            ·
              rfl

theorem cell23_989151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 12].length) (baseStart_989151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989151 prefixEnd_989151 := by exact prefixLift 989151
  have htrace : WordTrace (prefixWord ++ tailWord_989151) baseStart_989151 baseEnd_989151 := by
    simpa [prefixWord, tailWord_989151, baseEnd_989151] using wordTrace_append hprefix tailTrace_989151
  have hstable : (prefixWord ++ tailWord_989151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989151).length < 2 ^ (prefixWord ++ tailWord_989151).sum := by decide
  have hdescent : baseEnd_989151 < baseStart_989151 := by decide
  rcases family_descends (prefixWord ++ tailWord_989151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989155 : List Nat := [1, 1, 1, 6, 1, 2, 1, 4, 2, 4]
def baseStart_989155 : Nat := 118140960795 + 989155 * 2 ^ 59
def prefixEnd_989155 : Nat := 4983230072969 + 3 ^ 40 * 989155 * 2
def baseEnd_989155 : Nat := 169303985599394220071155

theorem tailTrace_989155 : CollatzResearch.WordTrace tailWord_989155 prefixEnd_989155 169303985599394220071155 := by
  unfold tailWord_989155
  simp only [CollatzResearch.WordTrace]
  refine ⟨36077446731467844069568919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24051631154311896046379279 36077446731467844069568919)
  ·
    refine ⟨54116170097201766104353379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36077446731467844069568919 54116170097201766104353379)
    ·
      refine ⟨81174255145802649156530069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54116170097201766104353379 81174255145802649156530069)
      ·
        refine ⟨3805043209959499179212347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 81174255145802649156530069 3805043209959499179212347)
        ·
          refine ⟨5707564814939248768818521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3805043209959499179212347 5707564814939248768818521)
          ·
            refine ⟨4280673611204436576613891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5707564814939248768818521 4280673611204436576613891)
            ·
              refine ⟨6421010416806654864920837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4280673611204436576613891 6421010416806654864920837)
              ·
                refine ⟨1203939453151247787172657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6421010416806654864920837 1203939453151247787172657)
                ·
                  refine ⟨902954589863435840379493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1203939453151247787172657 902954589863435840379493)
                  ·
                    refine ⟨169303985599394220071155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 902954589863435840379493 169303985599394220071155)
                    ·
                      rfl

theorem cell23_989155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 4, 2, 4].length) (baseStart_989155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989155 prefixEnd_989155 := by exact prefixLift 989155
  have htrace : WordTrace (prefixWord ++ tailWord_989155) baseStart_989155 baseEnd_989155 := by
    simpa [prefixWord, tailWord_989155, baseEnd_989155] using wordTrace_append hprefix tailTrace_989155
  have hstable : (prefixWord ++ tailWord_989155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989155).length < 2 ^ (prefixWord ++ tailWord_989155).sum := by decide
  have hdescent : baseEnd_989155 < baseStart_989155 := by decide
  rcases family_descends (prefixWord ++ tailWord_989155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989162 : List Nat := [3, 1, 3, 1, 2, 1, 2, 3, 3, 2, 2]
def baseStart_989162 : Nat := 118140960795 + 989162 * 2 ^ 59
def prefixEnd_989162 : Nat := 4983230072969 + 3 ^ 40 * 989162 * 2
def baseEnd_989162 : Nat := 507915551162764132825933

theorem tailTrace_989162 : CollatzResearch.WordTrace tailWord_989162 prefixEnd_989162 507915551162764132825933 := by
  unfold tailWord_989162
  simp only [CollatzResearch.WordTrace]
  refine ⟨9019425510610621066268435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24051801361628322843382493 9019425510610621066268435)
  ·
    refine ⟨13529138265915931599402653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9019425510610621066268435 13529138265915931599402653)
    ·
      refine ⟨5073426849718474349775995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13529138265915931599402653 5073426849718474349775995)
      ·
        refine ⟨7610140274577711524663993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5073426849718474349775995 7610140274577711524663993)
        ·
          refine ⟨5707605205933283643497995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7610140274577711524663993 5707605205933283643497995)
          ·
            refine ⟨8561407808899925465246993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5707605205933283643497995 8561407808899925465246993)
            ·
              refine ⟨6421055856674944098935245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8561407808899925465246993 6421055856674944098935245)
              ·
                refine ⟨2407895946253104037100717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6421055856674944098935245 2407895946253104037100717)
                ·
                  refine ⟨902960979844914013912769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2407895946253104037100717 902960979844914013912769)
                  ·
                    refine ⟨677220734883685510434577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 902960979844914013912769 677220734883685510434577)
                    ·
                      refine ⟨507915551162764132825933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 677220734883685510434577 507915551162764132825933)
                      ·
                        rfl

theorem cell23_989162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 3, 2, 2].length) (baseStart_989162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989162 prefixEnd_989162 := by exact prefixLift 989162
  have htrace : WordTrace (prefixWord ++ tailWord_989162) baseStart_989162 baseEnd_989162 := by
    simpa [prefixWord, tailWord_989162, baseEnd_989162] using wordTrace_append hprefix tailTrace_989162
  have hstable : (prefixWord ++ tailWord_989162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989162).length < 2 ^ (prefixWord ++ tailWord_989162).sum := by decide
  have hdescent : baseEnd_989162 < baseStart_989162 := by decide
  rcases family_descends (prefixWord ++ tailWord_989162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989171 : List Nat := [1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 6]
def baseStart_989171 : Nat := 118140960795 + 989171 * 2 ^ 59
def prefixEnd_989171 : Nat := 4983230072969 + 3 ^ 40 * 989171 * 2
def baseEnd_989171 : Nat := 507920172488654597613391

theorem tailTrace_989171 : CollatzResearch.WordTrace tailWord_989171 prefixEnd_989171 507920172488654597613391 := by
  unfold tailWord_989171
  simp only [CollatzResearch.WordTrace]
  refine ⟨36078030299409878802151367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24052020199606585868100911 36078030299409878802151367)
  ·
    refine ⟨54117045449114818203227051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36078030299409878802151367 54117045449114818203227051)
    ·
      refine ⟨81175568173672227304840577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54117045449114818203227051 81175568173672227304840577)
      ·
        refine ⟨60881676130254170478630433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81175568173672227304840577 60881676130254170478630433)
        ·
          refine ⟨45661257097690627858972825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60881676130254170478630433 45661257097690627858972825)
          ·
            refine ⟨34245942823267970894229619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45661257097690627858972825 34245942823267970894229619)
            ·
              refine ⟨51368914234901956341344429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34245942823267970894229619 51368914234901956341344429)
              ·
                refine ⟨19263342838088233628004161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51368914234901956341344429 19263342838088233628004161)
                ·
                  refine ⟨14447507128566175221003121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19263342838088233628004161 14447507128566175221003121)
                  ·
                    refine ⟨10835630346424631415752341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14447507128566175221003121 10835630346424631415752341)
                    ·
                      refine ⟨507920172488654597613391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10835630346424631415752341 507920172488654597613391)
                      ·
                        rfl

theorem cell23_989171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 6].length) (baseStart_989171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989171 prefixEnd_989171 := by exact prefixLift 989171
  have htrace : WordTrace (prefixWord ++ tailWord_989171) baseStart_989171 baseEnd_989171 := by
    simpa [prefixWord, tailWord_989171, baseEnd_989171] using wordTrace_append hprefix tailTrace_989171
  have hstable : (prefixWord ++ tailWord_989171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989171).length < 2 ^ (prefixWord ++ tailWord_989171).sum := by decide
  have hdescent : baseEnd_989171 < baseStart_989171 := by decide
  rcases family_descends (prefixWord ++ tailWord_989171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989182 : List Nat := [4, 2, 2, 2, 1, 1, 2, 1, 3, 2, 3]
def baseStart_989182 : Nat := 118140960795 + 989182 * 2 ^ 59
def prefixEnd_989182 : Nat := 4983230072969 + 3 ^ 40 * 989182 * 2
def baseEnd_989182 : Nat := 507925820775854054575841

theorem tailTrace_989182 : CollatzResearch.WordTrace tailWord_989182 prefixEnd_989182 507925820775854054575841 := by
  unfold tailWord_989182
  simp only [CollatzResearch.WordTrace]
  refine ⟨4509803937796253460100225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24052287668246685120534533 4509803937796253460100225)
  ·
    refine ⟨3382352953347190095075169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4509803937796253460100225 3382352953347190095075169)
    ·
      refine ⟨2536764715010392571306377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3382352953347190095075169 2536764715010392571306377)
      ·
        refine ⟨1902573536257794428479783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2536764715010392571306377 1902573536257794428479783)
        ·
          refine ⟨2853860304386691642719675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1902573536257794428479783 2853860304386691642719675)
          ·
            refine ⟨4280790456580037464079513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2853860304386691642719675 4280790456580037464079513)
            ·
              refine ⟨3210592842435028098059635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4280790456580037464079513 3210592842435028098059635)
              ·
                refine ⟨4815889263652542147089453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3210592842435028098059635 4815889263652542147089453)
                ·
                  refine ⟨1805958473869703305158545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4815889263652542147089453 1805958473869703305158545)
                  ·
                    refine ⟨1354468855402277478868909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1805958473869703305158545 1354468855402277478868909)
                    ·
                      refine ⟨507925820775854054575841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1354468855402277478868909 507925820775854054575841)
                      ·
                        rfl

theorem cell23_989182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_989182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989182 prefixEnd_989182 := by exact prefixLift 989182
  have htrace : WordTrace (prefixWord ++ tailWord_989182) baseStart_989182 baseEnd_989182 := by
    simpa [prefixWord, tailWord_989182, baseEnd_989182] using wordTrace_append hprefix tailTrace_989182
  have hstable : (prefixWord ++ tailWord_989182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989182).length < 2 ^ (prefixWord ++ tailWord_989182).sum := by decide
  have hdescent : baseEnd_989182 < baseStart_989182 := by decide
  rcases family_descends (prefixWord ++ tailWord_989182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989195 : List Nat := [1, 1, 1, 1, 6, 1, 2, 2, 4, 1, 3]
def baseStart_989195 : Nat := 118140960795 + 989195 * 2 ^ 59
def prefixEnd_989195 : Nat := 4983230072969 + 3 ^ 40 * 989195 * 2
def baseEnd_989195 : Nat := 507932496024362503713281

theorem tailTrace_989195 : CollatzResearch.WordTrace tailWord_989195 prefixEnd_989195 507932496024362503713281 := by
  unfold tailWord_989195
  simp only [CollatzResearch.WordTrace]
  refine ⟨36078905651322930901025039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24052603767548620600683359 36078905651322930901025039)
  ·
    refine ⟨54118358476984396351537559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36078905651322930901025039 54118358476984396351537559)
    ·
      refine ⟨81177537715476594527306339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54118358476984396351537559 81177537715476594527306339)
      ·
        refine ⟨121766306573214891790959509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81177537715476594527306339 121766306573214891790959509)
        ·
          refine ⟨5707795620619448052701227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 121766306573214891790959509 5707795620619448052701227)
          ·
            refine ⟨8561693430929172079051841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5707795620619448052701227 8561693430929172079051841)
            ·
              refine ⟨6421270073196879059288881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8561693430929172079051841 6421270073196879059288881)
              ·
                refine ⟨4815952554897659294466661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6421270073196879059288881 4815952554897659294466661)
                ·
                  refine ⟨902991104043311117712499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4815952554897659294466661 902991104043311117712499)
                  ·
                    refine ⟨1354486656064966676568749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 902991104043311117712499 1354486656064966676568749)
                    ·
                      refine ⟨507932496024362503713281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1354486656064966676568749 507932496024362503713281)
                      ·
                        rfl

theorem cell23_989195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 4, 1, 3].length) (baseStart_989195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989195 prefixEnd_989195 := by exact prefixLift 989195
  have htrace : WordTrace (prefixWord ++ tailWord_989195) baseStart_989195 baseEnd_989195 := by
    simpa [prefixWord, tailWord_989195, baseEnd_989195] using wordTrace_append hprefix tailTrace_989195
  have hstable : (prefixWord ++ tailWord_989195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989195).length < 2 ^ (prefixWord ++ tailWord_989195).sum := by decide
  have hdescent : baseEnd_989195 < baseStart_989195 := by decide
  rcases family_descends (prefixWord ++ tailWord_989195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989212 : List Nat := [2, 2, 3, 1, 3, 2, 1, 1, 4, 1, 3]
def baseStart_989212 : Nat := 118140960795 + 989212 * 2 ^ 59
def prefixEnd_989212 : Nat := 4983230072969 + 3 ^ 40 * 989212 * 2
def baseEnd_989212 : Nat := 507941225195488937200703

theorem tailTrace_989212 : CollatzResearch.WordTrace tailWord_989212 prefixEnd_989212 507941225195488937200703 := by
  unfold tailWord_989212
  simp only [CollatzResearch.WordTrace]
  refine ⟨18039762846130671402196945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24053017128174228536262593 18039762846130671402196945)
  ·
    refine ⟨13529822134598003551647709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18039762846130671402196945 13529822134598003551647709)
    ·
      refine ⟨5073683300474251331867891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13529822134598003551647709 5073683300474251331867891)
      ·
        refine ⟨7610524950711376997801837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5073683300474251331867891 7610524950711376997801837)
        ·
          refine ⟨2853946856516766374175689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7610524950711376997801837 2853946856516766374175689)
          ·
            refine ⟨2140460142387574780631767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2853946856516766374175689 2140460142387574780631767)
            ·
              refine ⟨3210690213581362170947651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2140460142387574780631767 3210690213581362170947651)
              ·
                refine ⟨4816035320372043256421477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3210690213581362170947651 4816035320372043256421477)
                ·
                  refine ⟨903006622569758110579027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4816035320372043256421477 903006622569758110579027)
                  ·
                    refine ⟨1354509933854637165868541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 903006622569758110579027 1354509933854637165868541)
                    ·
                      refine ⟨507941225195488937200703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1354509933854637165868541 507941225195488937200703)
                      ·
                        rfl

theorem cell23_989212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_989212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989212 prefixEnd_989212 := by exact prefixLift 989212
  have htrace : WordTrace (prefixWord ++ tailWord_989212) baseStart_989212 baseEnd_989212 := by
    simpa [prefixWord, tailWord_989212, baseEnd_989212] using wordTrace_append hprefix tailTrace_989212
  have hstable : (prefixWord ++ tailWord_989212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989212).length < 2 ^ (prefixWord ++ tailWord_989212).sum := by decide
  have hdescent : baseEnd_989212 < baseStart_989212 := by decide
  rcases family_descends (prefixWord ++ tailWord_989212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989268 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 1, 1, 9]
def baseStart_989268 : Nat := 118140960795 + 989268 * 2 ^ 59
def prefixEnd_989268 : Nat := 4983230072969 + 3 ^ 40 * 989268 * 2
def baseEnd_989268 : Nat := 507969980112140718100445

theorem tailTrace_989268 : CollatzResearch.WordTrace tailWord_989268 prefixEnd_989268 507969980112140718100445 := by
  unfold tailWord_989268
  simp only [CollatzResearch.WordTrace]
  refine ⟨18040784090029232184216229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24054378786705642912288305 18040784090029232184216229)
  ·
    refine ⟨3382647016880481034540543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18040784090029232184216229 3382647016880481034540543)
    ·
      refine ⟨5073970525320721551810815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3382647016880481034540543 5073970525320721551810815)
      ·
        refine ⟨7610955787981082327716223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5073970525320721551810815 7610955787981082327716223)
        ·
          refine ⟨11416433681971623491574335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7610955787981082327716223 11416433681971623491574335)
          ·
            refine ⟨17124650522957435237361503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11416433681971623491574335 17124650522957435237361503)
            ·
              refine ⟨25686975784436152856042255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17124650522957435237361503 25686975784436152856042255)
              ·
                refine ⟨38530463676654229284063383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25686975784436152856042255 38530463676654229284063383)
                ·
                  refine ⟨57795695514981343926095075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38530463676654229284063383 57795695514981343926095075)
                  ·
                    refine ⟨86693543272472015889142613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57795695514981343926095075 86693543272472015889142613)
                    ·
                      refine ⟨507969980112140718100445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 86693543272472015889142613 507969980112140718100445)
                      ·
                        rfl

theorem cell23_989268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_989268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989268 prefixEnd_989268 := by exact prefixLift 989268
  have htrace : WordTrace (prefixWord ++ tailWord_989268) baseStart_989268 baseEnd_989268 := by
    simpa [prefixWord, tailWord_989268, baseEnd_989268] using wordTrace_append hprefix tailTrace_989268
  have hstable : (prefixWord ++ tailWord_989268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989268).length < 2 ^ (prefixWord ++ tailWord_989268).sum := by decide
  have hdescent : baseEnd_989268 < baseStart_989268 := by decide
  rcases family_descends (prefixWord ++ tailWord_989268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989305 : List Nat := [1, 2, 1, 3, 4, 1, 1, 3, 2, 5]
def baseStart_989305 : Nat := 118140960795 + 989305 * 2 ^ 59
def prefixEnd_989305 : Nat := 4983230072969 + 3 ^ 40 * 989305 * 2
def baseEnd_989305 : Nat := 169329659632119024445925

theorem tailTrace_989305 : CollatzResearch.WordTrace tailWord_989305 prefixEnd_989305 169329659632119024445925 := by
  unfold tailWord_989305
  simp only [CollatzResearch.WordTrace]
  refine ⟨36082917680924419687529369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24055278453949613125019579 36082917680924419687529369)
  ·
    refine ⟨27062188260693314765647027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36082917680924419687529369 27062188260693314765647027)
    ·
      refine ⟨40593282391039972148470541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27062188260693314765647027 40593282391039972148470541)
      ·
        refine ⟨15222480896639989555676453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40593282391039972148470541 15222480896639989555676453)
        ·
          refine ⟨2854215168119998041689335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15222480896639989555676453 2854215168119998041689335)
          ·
            refine ⟨4281322752179997062534003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2854215168119998041689335 4281322752179997062534003)
            ·
              refine ⟨6421984128269995593801005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4281322752179997062534003 6421984128269995593801005)
              ·
                refine ⟨2408244048101248347675377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6421984128269995593801005 2408244048101248347675377)
                ·
                  refine ⟨1806183036075936260756533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2408244048101248347675377 1806183036075936260756533)
                  ·
                    refine ⟨169329659632119024445925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1806183036075936260756533 169329659632119024445925)
                    ·
                      rfl

theorem cell23_989305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 2, 5].length) (baseStart_989305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989305 prefixEnd_989305 := by exact prefixLift 989305
  have htrace : WordTrace (prefixWord ++ tailWord_989305) baseStart_989305 baseEnd_989305 := by
    simpa [prefixWord, tailWord_989305, baseEnd_989305] using wordTrace_append hprefix tailTrace_989305
  have hstable : (prefixWord ++ tailWord_989305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989305).length < 2 ^ (prefixWord ++ tailWord_989305).sum := by decide
  have hdescent : baseEnd_989305 < baseStart_989305 := by decide
  rcases family_descends (prefixWord ++ tailWord_989305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989326 : List Nat := [4, 1, 1, 3, 3, 2, 2, 2, 5]
def baseStart_989326 : Nat := 118140960795 + 989326 * 2 ^ 59
def prefixEnd_989326 : Nat := 4983230072969 + 3 ^ 40 * 989326 * 2
def baseEnd_989326 : Nat := 56444417998900165686131

theorem tailTrace_989326 : CollatzResearch.WordTrace tailWord_989326 prefixEnd_989326 56444417998900165686131 := by
  unfold tailWord_989326
  simp only [CollatzResearch.WordTrace]
  refine ⟨4510460451731042534255479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24055789075898893516029221 4510460451731042534255479)
  ·
    refine ⟨6765690677596563801383219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4510460451731042534255479 6765690677596563801383219)
    ·
      refine ⟨10148536016394845702074829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6765690677596563801383219 10148536016394845702074829)
      ·
        refine ⟨3805701006148067138278061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10148536016394845702074829 3805701006148067138278061)
        ·
          refine ⟨1427137877305525176854273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3805701006148067138278061 1427137877305525176854273)
          ·
            refine ⟨1070353407979143882640705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1427137877305525176854273 1070353407979143882640705)
            ·
              refine ⟨802765055984357911980529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1070353407979143882640705 802765055984357911980529)
              ·
                refine ⟨602073791988268433985397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 802765055984357911980529 602073791988268433985397)
                ·
                  refine ⟨56444417998900165686131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 602073791988268433985397 56444417998900165686131)
                  ·
                    rfl

theorem cell23_989326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 2, 5].length) (baseStart_989326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989326 prefixEnd_989326 := by exact prefixLift 989326
  have htrace : WordTrace (prefixWord ++ tailWord_989326) baseStart_989326 baseEnd_989326 := by
    simpa [prefixWord, tailWord_989326, baseEnd_989326] using wordTrace_append hprefix tailTrace_989326
  have hstable : (prefixWord ++ tailWord_989326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989326).length < 2 ^ (prefixWord ++ tailWord_989326).sum := by decide
  have hdescent : baseEnd_989326 < baseStart_989326 := by decide
  rcases family_descends (prefixWord ++ tailWord_989326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989328 : List Nat := [2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 5]
def baseStart_989328 : Nat := 118140960795 + 989328 * 2 ^ 59
def prefixEnd_989328 : Nat := 4983230072969 + 3 ^ 40 * 989328 * 2
def baseEnd_989328 : Nat := 508000788951410483350169

theorem tailTrace_989328 : CollatzResearch.WordTrace tailWord_989328 prefixEnd_989328 508000788951410483350169 := by
  unfold tailWord_989328
  simp only [CollatzResearch.WordTrace]
  refine ⟨18041878279920547307808319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24055837706560729743744425 18041878279920547307808319)
  ·
    refine ⟨27062817419880820961712479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18041878279920547307808319 27062817419880820961712479)
    ·
      refine ⟨40594226129821231442568719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27062817419880820961712479 40594226129821231442568719)
      ·
        refine ⟨60891339194731847163853079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40594226129821231442568719 60891339194731847163853079)
        ·
          refine ⟨91337008792097770745779619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60891339194731847163853079 91337008792097770745779619)
          ·
            refine ⟨137005513188146656118669429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91337008792097770745779619 137005513188146656118669429)
            ·
              refine ⟨12844266861388749011125259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137005513188146656118669429 12844266861388749011125259)
              ·
                refine ⟨19266400292083123516687889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12844266861388749011125259 19266400292083123516687889)
                ·
                  refine ⟨14449800219062342637515917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19266400292083123516687889 14449800219062342637515917)
                  ·
                    refine ⟨5418675082148378489068469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14449800219062342637515917 5418675082148378489068469)
                    ·
                      refine ⟨508000788951410483350169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5418675082148378489068469 508000788951410483350169)
                      ·
                        rfl

theorem cell23_989328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 5].length) (baseStart_989328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989328 prefixEnd_989328 := by exact prefixLift 989328
  have htrace : WordTrace (prefixWord ++ tailWord_989328) baseStart_989328 baseEnd_989328 := by
    simpa [prefixWord, tailWord_989328, baseEnd_989328] using wordTrace_append hprefix tailTrace_989328
  have hstable : (prefixWord ++ tailWord_989328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989328).length < 2 ^ (prefixWord ++ tailWord_989328).sum := by decide
  have hdescent : baseEnd_989328 < baseStart_989328 := by decide
  rcases family_descends (prefixWord ++ tailWord_989328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989369 : List Nat := [1, 2, 1, 4, 1, 2, 4, 3, 1, 4]
def baseStart_989369 : Nat := 118140960795 + 989369 * 2 ^ 59
def prefixEnd_989369 : Nat := 4983230072969 + 3 ^ 40 * 989369 * 2
def baseEnd_989369 : Nat := 169340613886081607645827

theorem tailTrace_989369 : CollatzResearch.WordTrace tailWord_989369 prefixEnd_989369 169340613886081607645827 := by
  unfold tailWord_989369
  simp only [CollatzResearch.WordTrace]
  refine ⟨36085251952692558617859161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24056834635128372411906107 36085251952692558617859161)
  ·
    refine ⟨27063938964519418963394371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36085251952692558617859161 27063938964519418963394371)
    ·
      refine ⟨40595908446779128445091557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27063938964519418963394371 40595908446779128445091557)
      ·
        refine ⟨7611732833771086583454667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40595908446779128445091557 7611732833771086583454667)
        ·
          refine ⟨11417599250656629875182001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7611732833771086583454667 11417599250656629875182001)
          ·
            refine ⟨8563199437992472406386501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11417599250656629875182001 8563199437992472406386501)
            ·
              refine ⟨1605599894623588576197469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8563199437992472406386501 1605599894623588576197469)
              ·
                refine ⟨602099960483845716074051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1605599894623588576197469 602099960483845716074051)
                ·
                  refine ⟨903149940725768574111077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 602099960483845716074051 903149940725768574111077)
                  ·
                    refine ⟨169340613886081607645827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 903149940725768574111077 169340613886081607645827)
                    ·
                      rfl

theorem cell23_989369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 3, 1, 4].length) (baseStart_989369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989369 prefixEnd_989369 := by exact prefixLift 989369
  have htrace : WordTrace (prefixWord ++ tailWord_989369) baseStart_989369 baseEnd_989369 := by
    simpa [prefixWord, tailWord_989369, baseEnd_989369] using wordTrace_append hprefix tailTrace_989369
  have hstable : (prefixWord ++ tailWord_989369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989369).length < 2 ^ (prefixWord ++ tailWord_989369).sum := by decide
  have hdescent : baseEnd_989369 < baseStart_989369 := by decide
  rcases family_descends (prefixWord ++ tailWord_989369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989402 : List Nat := [3, 1, 1, 2, 2, 1, 3, 2, 1, 5, 2]
def baseStart_989402 : Nat := 118140960795 + 989402 * 2 ^ 59
def prefixEnd_989402 : Nat := 4983230072969 + 3 ^ 40 * 989402 * 2
def baseEnd_989402 : Nat := 508038786519843193824829

theorem tailTrace_989402 : CollatzResearch.WordTrace tailWord_989402 prefixEnd_989402 508038786519843193824829 := by
  unfold tailWord_989402
  simp only [CollatzResearch.WordTrace]
  refine ⟨9021613890393251313452615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24057637041048670169206973 9021613890393251313452615)
  ·
    refine ⟨13532420835589876970178923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9021613890393251313452615 13532420835589876970178923)
    ·
      refine ⟨20298631253384815455268385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13532420835589876970178923 20298631253384815455268385)
      ·
        refine ⟨15223973440038611591451289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20298631253384815455268385 15223973440038611591451289)
        ·
          refine ⟨11417980080028958693588467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15223973440038611591451289 11417980080028958693588467)
          ·
            refine ⟨17126970120043438040382701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11417980080028958693588467 17126970120043438040382701)
            ·
              refine ⟨6422613795016289265143513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17126970120043438040382701 6422613795016289265143513)
              ·
                refine ⟨4816960346262216948857635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6422613795016289265143513 4816960346262216948857635)
                ·
                  refine ⟨7225440519393325423286453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4816960346262216948857635 7225440519393325423286453)
                  ·
                    refine ⟨677385048693124258433105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7225440519393325423286453 677385048693124258433105)
                    ·
                      refine ⟨508038786519843193824829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 677385048693124258433105 508038786519843193824829)
                      ·
                        rfl

theorem cell23_989402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 1, 5, 2].length) (baseStart_989402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989402 prefixEnd_989402 := by exact prefixLift 989402
  have htrace : WordTrace (prefixWord ++ tailWord_989402) baseStart_989402 baseEnd_989402 := by
    simpa [prefixWord, tailWord_989402, baseEnd_989402] using wordTrace_append hprefix tailTrace_989402
  have hstable : (prefixWord ++ tailWord_989402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989402).length < 2 ^ (prefixWord ++ tailWord_989402).sum := by decide
  have hdescent : baseEnd_989402 < baseStart_989402 := by decide
  rcases family_descends (prefixWord ++ tailWord_989402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989425 : List Nat := [1, 2, 2, 2, 2, 1, 2, 4, 1, 6]
def baseStart_989425 : Nat := 118140960795 + 989425 * 2 ^ 59
def prefixEnd_989425 : Nat := 4983230072969 + 3 ^ 40 * 989425 * 2
def baseEnd_989425 : Nat := 169350198858298867945741

theorem tailTrace_989425 : CollatzResearch.WordTrace tailWord_989425 prefixEnd_989425 169350198858298867945741 := by
  unfold tailWord_989425
  simp only [CollatzResearch.WordTrace]
  refine ⟨36087294440489680181897729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24058196293659786787931819 36087294440489680181897729)
  ·
    refine ⟨27065470830367260136423297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36087294440489680181897729 27065470830367260136423297)
    ·
      refine ⟨20299103122775445102317473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27065470830367260136423297 20299103122775445102317473)
      ·
        refine ⟨15224327342081583826738105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20299103122775445102317473 15224327342081583826738105)
        ·
          refine ⟨11418245506561187870053579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15224327342081583826738105 11418245506561187870053579)
          ·
            refine ⟨17127368259841781805080369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11418245506561187870053579 17127368259841781805080369)
            ·
              refine ⟨12845526194881336353810277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17127368259841781805080369 12845526194881336353810277)
              ·
                refine ⟨2408536161540250566339427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12845526194881336353810277 2408536161540250566339427)
                ·
                  refine ⟨3612804242310375849509141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2408536161540250566339427 3612804242310375849509141)
                  ·
                    refine ⟨169350198858298867945741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3612804242310375849509141 169350198858298867945741)
                    ·
                      rfl

theorem cell23_989425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 6].length) (baseStart_989425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989425 prefixEnd_989425 := by exact prefixLift 989425
  have htrace : WordTrace (prefixWord ++ tailWord_989425) baseStart_989425 baseEnd_989425 := by
    simpa [prefixWord, tailWord_989425, baseEnd_989425] using wordTrace_append hprefix tailTrace_989425
  have hstable : (prefixWord ++ tailWord_989425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989425).length < 2 ^ (prefixWord ++ tailWord_989425).sum := by decide
  have hdescent : baseEnd_989425 < baseStart_989425 := by decide
  rcases family_descends (prefixWord ++ tailWord_989425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989445 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 5, 2, 4]
def baseStart_989445 : Nat := 118140960795 + 989445 * 2 ^ 59
def prefixEnd_989445 : Nat := 4983230072969 + 3 ^ 40 * 989445 * 2
def baseEnd_989445 : Nat := 508060866187986525587131

theorem tailTrace_989445 : CollatzResearch.WordTrace tailWord_989445 prefixEnd_989445 508060866187986525587131 := by
  unfold tailWord_989445
  simp only [CollatzResearch.WordTrace]
  refine ⟨36088023900417223597625789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24058682600278149065083859 36088023900417223597625789)
  ·
    refine ⟨13533008962656458849109671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36088023900417223597625789 13533008962656458849109671)
    ·
      refine ⟨20299513443984688273664507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13533008962656458849109671 20299513443984688273664507)
      ·
        refine ⟨30449270165977032410496761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20299513443984688273664507 30449270165977032410496761)
        ·
          refine ⟨22836952624482774307872571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30449270165977032410496761 22836952624482774307872571)
          ·
            refine ⟨34255428936724161461808857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22836952624482774307872571 34255428936724161461808857)
            ·
              refine ⟨25691571702543121096356643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34255428936724161461808857 25691571702543121096356643)
              ·
                refine ⟨38537357553814681644534965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25691571702543121096356643 38537357553814681644534965)
                ·
                  refine ⟨3612877270670126404175153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38537357553814681644534965 3612877270670126404175153)
                  ·
                    refine ⟨2709657953002594803131365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3612877270670126404175153 2709657953002594803131365)
                    ·
                      refine ⟨508060866187986525587131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2709657953002594803131365 508060866187986525587131)
                      ·
                        rfl

theorem cell23_989445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 2, 4].length) (baseStart_989445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989445 prefixEnd_989445 := by exact prefixLift 989445
  have htrace : WordTrace (prefixWord ++ tailWord_989445) baseStart_989445 baseEnd_989445 := by
    simpa [prefixWord, tailWord_989445, baseEnd_989445] using wordTrace_append hprefix tailTrace_989445
  have hstable : (prefixWord ++ tailWord_989445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989445).length < 2 ^ (prefixWord ++ tailWord_989445).sum := by decide
  have hdescent : baseEnd_989445 < baseStart_989445 := by decide
  rcases family_descends (prefixWord ++ tailWord_989445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989452 : List Nat := [2, 2, 1, 2, 2, 2, 2, 2, 3, 2, 3]
def baseStart_989452 : Nat := 118140960795 + 989452 * 2 ^ 59
def prefixEnd_989452 : Nat := 4983230072969 + 3 ^ 40 * 989452 * 2
def baseEnd_989452 : Nat := 508064460552567998199599

theorem tailTrace_989452 : CollatzResearch.WordTrace tailWord_989452 prefixEnd_989452 508064460552567998199599 := by
  unfold tailWord_989452
  simp only [CollatzResearch.WordTrace]
  refine ⟨18044139605695931896565305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24058852807594575862087073 18044139605695931896565305)
  ·
    refine ⟨13533104704271948922423979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18044139605695931896565305 13533104704271948922423979)
    ·
      refine ⟨20299657056407923383635969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13533104704271948922423979 20299657056407923383635969)
      ·
        refine ⟨15224742792305942537726977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20299657056407923383635969 15224742792305942537726977)
        ·
          refine ⟨11418557094229456903295233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15224742792305942537726977 11418557094229456903295233)
          ·
            refine ⟨8563917820672092677471425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11418557094229456903295233 8563917820672092677471425)
            ·
              refine ⟨6422938365504069508103569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8563917820672092677471425 6422938365504069508103569)
              ·
                refine ⟨4817203774128052131077677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6422938365504069508103569 4817203774128052131077677)
                ·
                  refine ⟨1806451415298019549154129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4817203774128052131077677 1806451415298019549154129)
                  ·
                    refine ⟨1354838561473514661865597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1806451415298019549154129 1354838561473514661865597)
                    ·
                      refine ⟨508064460552567998199599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1354838561473514661865597 508064460552567998199599)
                      ·
                        rfl

theorem cell23_989452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 3, 2, 3].length) (baseStart_989452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989452 prefixEnd_989452 := by exact prefixLift 989452
  have htrace : WordTrace (prefixWord ++ tailWord_989452) baseStart_989452 baseEnd_989452 := by
    simpa [prefixWord, tailWord_989452, baseEnd_989452] using wordTrace_append hprefix tailTrace_989452
  have hstable : (prefixWord ++ tailWord_989452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989452).length < 2 ^ (prefixWord ++ tailWord_989452).sum := by decide
  have hdescent : baseEnd_989452 < baseStart_989452 := by decide
  rcases family_descends (prefixWord ++ tailWord_989452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989466 : List Nat := [3, 1, 1, 3, 4, 2, 1, 2, 1, 1, 4]
def baseStart_989466 : Nat := 118140960795 + 989466 * 2 ^ 59
def prefixEnd_989466 : Nat := 4983230072969 + 3 ^ 40 * 989466 * 2
def baseEnd_989466 : Nat := 508071649281730943424535

theorem tailTrace_989466 : CollatzResearch.WordTrace tailWord_989466 prefixEnd_989466 508071649281730943424535 := by
  unfold tailWord_989466
  simp only [CollatzResearch.WordTrace]
  refine ⟨9022197458335286046035063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24059193222227429456093501 9022197458335286046035063)
  ·
    refine ⟨13533296187502929069052595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9022197458335286046035063 13533296187502929069052595)
    ·
      refine ⟨20299944281254393603578893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13533296187502929069052595 20299944281254393603578893)
      ·
        refine ⟨7612479105470397601342085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20299944281254393603578893 7612479105470397601342085)
        ·
          refine ⟨1427339832275699550251641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7612479105470397601342085 1427339832275699550251641)
          ·
            refine ⟨1070504874206774662688731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1427339832275699550251641 1070504874206774662688731)
            ·
              refine ⟨1605757311310161994033097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1070504874206774662688731 1605757311310161994033097)
              ·
                refine ⟨1204317983482621495524823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1605757311310161994033097 1204317983482621495524823)
                ·
                  refine ⟨1806476975223932243287235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1204317983482621495524823 1806476975223932243287235)
                  ·
                    refine ⟨2709715462835898364930853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1806476975223932243287235 2709715462835898364930853)
                    ·
                      refine ⟨508071649281730943424535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2709715462835898364930853 508071649281730943424535)
                      ·
                        rfl

theorem cell23_989466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_989466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989466 prefixEnd_989466 := by exact prefixLift 989466
  have htrace : WordTrace (prefixWord ++ tailWord_989466) baseStart_989466 baseEnd_989466 := by
    simpa [prefixWord, tailWord_989466, baseEnd_989466] using wordTrace_append hprefix tailTrace_989466
  have hstable : (prefixWord ++ tailWord_989466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989466).length < 2 ^ (prefixWord ++ tailWord_989466).sum := by decide
  have hdescent : baseEnd_989466 < baseStart_989466 := by decide
  rcases family_descends (prefixWord ++ tailWord_989466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989495 : List Nat := [1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 5]
def baseStart_989495 : Nat := 118140960795 + 989495 * 2 ^ 59
def prefixEnd_989495 : Nat := 4983230072969 + 3 ^ 40 * 989495 * 2
def baseEnd_989495 : Nat := 508086540220711329961901

theorem tailTrace_989495 : CollatzResearch.WordTrace tailWord_989495 prefixEnd_989495 508086540220711329961901 := by
  unfold tailWord_989495
  simp only [CollatzResearch.WordTrace]
  refine ⟨36089847550236082136945939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24059898366824054757963959 36089847550236082136945939)
  ·
    refine ⟨54134771325354123205418909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36089847550236082136945939 54134771325354123205418909)
    ·
      refine ⟨20300539247007796202032091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54134771325354123205418909 20300539247007796202032091)
      ·
        refine ⟨30450808870511694303048137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20300539247007796202032091 30450808870511694303048137)
        ·
          refine ⟨22838106652883770727286103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30450808870511694303048137 22838106652883770727286103)
          ·
            refine ⟨34257159979325656090929155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22838106652883770727286103 34257159979325656090929155)
            ·
              refine ⟨51385739968988484136393733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34257159979325656090929155 51385739968988484136393733)
              ·
                refine ⟨9634826244185340775573825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51385739968988484136393733 9634826244185340775573825)
                ·
                  refine ⟨7226119683139005581680369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9634826244185340775573825 7226119683139005581680369)
                  ·
                    refine ⟨5419589762354254186260277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7226119683139005581680369 5419589762354254186260277)
                    ·
                      refine ⟨508086540220711329961901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5419589762354254186260277 508086540220711329961901)
                      ·
                        rfl

theorem cell23_989495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 5].length) (baseStart_989495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989495 prefixEnd_989495 := by exact prefixLift 989495
  have htrace : WordTrace (prefixWord ++ tailWord_989495) baseStart_989495 baseEnd_989495 := by
    simpa [prefixWord, tailWord_989495, baseEnd_989495] using wordTrace_append hprefix tailTrace_989495
  have hstable : (prefixWord ++ tailWord_989495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989495).length < 2 ^ (prefixWord ++ tailWord_989495).sum := by decide
  have hdescent : baseEnd_989495 < baseStart_989495 := by decide
  rcases family_descends (prefixWord ++ tailWord_989495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989502 : List Nat := [4, 2, 1, 2, 1, 2, 1, 1, 2, 7]
def baseStart_989502 : Nat := 118140960795 + 989502 * 2 ^ 59
def prefixEnd_989502 : Nat := 4983230072969 + 3 ^ 40 * 989502 * 2
def baseEnd_989502 : Nat := 169363378195097600858123

theorem tailTrace_989502 : CollatzResearch.WordTrace tailWord_989502 prefixEnd_989502 169363378195097600858123 := by
  unfold tailWord_989502
  simp only [CollatzResearch.WordTrace]
  refine ⟨4511262857651340291556345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24060068574140481554967173 4511262857651340291556345)
  ·
    refine ⟨3383447143238505218667259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4511262857651340291556345 3383447143238505218667259)
    ·
      refine ⟨5075170714857757828000889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3383447143238505218667259 5075170714857757828000889)
      ·
        refine ⟨3806378036143318371000667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5075170714857757828000889 3806378036143318371000667)
        ·
          refine ⟨5709567054214977556501001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3806378036143318371000667 5709567054214977556501001)
          ·
            refine ⟨4282175290661233167375751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5709567054214977556501001 4282175290661233167375751)
            ·
              refine ⟨6423262935991849751063627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4282175290661233167375751 6423262935991849751063627)
              ·
                refine ⟨9634894403987774626595441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6423262935991849751063627 9634894403987774626595441)
                ·
                  refine ⟨7226170802990830969946581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9634894403987774626595441 7226170802990830969946581)
                  ·
                    refine ⟨169363378195097600858123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7226170802990830969946581 169363378195097600858123)
                    ·
                      rfl

theorem cell23_989502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_989502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989502 prefixEnd_989502 := by exact prefixLift 989502
  have htrace : WordTrace (prefixWord ++ tailWord_989502) baseStart_989502 baseEnd_989502 := by
    simpa [prefixWord, tailWord_989502, baseEnd_989502] using wordTrace_append hprefix tailTrace_989502
  have hstable : (prefixWord ++ tailWord_989502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989502).length < 2 ^ (prefixWord ++ tailWord_989502).sum := by decide
  have hdescent : baseEnd_989502 < baseStart_989502 := by decide
  rcases family_descends (prefixWord ++ tailWord_989502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989534 : List Nat := [4, 4, 2, 1, 1, 2, 2, 1, 1, 1, 4]
def baseStart_989534 : Nat := 118140960795 + 989534 * 2 ^ 59
def prefixEnd_989534 : Nat := 4983230072969 + 3 ^ 40 * 989534 * 2
def baseEnd_989534 : Nat := 508106565966236677374223

theorem tailTrace_989534 : CollatzResearch.WordTrace tailWord_989534 prefixEnd_989534 508106565966236677374223 := by
  unfold tailWord_989534
  simp only [CollatzResearch.WordTrace]
  refine ⟨4511408749636848974701957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24060846664729861198410437 4511408749636848974701957)
  ·
    refine ⟨845889140556909182756617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4511408749636848974701957 845889140556909182756617)
    ·
      refine ⟨634416855417681887067463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 845889140556909182756617 634416855417681887067463)
      ·
        refine ⟨951625283126522830601195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 634416855417681887067463 951625283126522830601195)
        ·
          refine ⟨1427437924689784245901793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 951625283126522830601195 1427437924689784245901793)
          ·
            refine ⟨1070578443517338184426345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1427437924689784245901793 1070578443517338184426345)
            ·
              refine ⟨802933832638003638319759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1070578443517338184426345 802933832638003638319759)
              ·
                refine ⟨1204400748957005457479639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 802933832638003638319759 1204400748957005457479639)
                ·
                  refine ⟨1806601123435508186219459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1204400748957005457479639 1806601123435508186219459)
                  ·
                    refine ⟨2709901685153262279329189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1806601123435508186219459 2709901685153262279329189)
                    ·
                      refine ⟨508106565966236677374223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2709901685153262279329189 508106565966236677374223)
                      ·
                        rfl

theorem cell23_989534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_989534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989534 prefixEnd_989534 := by exact prefixLift 989534
  have htrace : WordTrace (prefixWord ++ tailWord_989534) baseStart_989534 baseEnd_989534 := by
    simpa [prefixWord, tailWord_989534, baseEnd_989534] using wordTrace_append hprefix tailTrace_989534
  have hstable : (prefixWord ++ tailWord_989534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989534).length < 2 ^ (prefixWord ++ tailWord_989534).sum := by decide
  have hdescent : baseEnd_989534 < baseStart_989534 := by decide
  rcases family_descends (prefixWord ++ tailWord_989534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989539 : List Nat := [1, 1, 1, 5, 2, 1, 1, 4, 1, 4, 2]
def baseStart_989539 : Nat := 118140960795 + 989539 * 2 ^ 59
def prefixEnd_989539 : Nat := 4983230072969 + 3 ^ 40 * 989539 * 2
def baseEnd_989539 : Nat := 508109133369509157811699

theorem tailTrace_989539 : CollatzResearch.WordTrace tailWord_989539 prefixEnd_989539 508109133369509157811699 := by
  unfold tailWord_989539
  simp only [CollatzResearch.WordTrace]
  refine ⟨36091452362076677651547671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24060968241384451767698447 36091452362076677651547671)
  ·
    refine ⟨54137178543115016477321507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36091452362076677651547671 54137178543115016477321507)
    ·
      refine ⟨81205767814672524715982261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54137178543115016477321507 81205767814672524715982261)
      ·
        refine ⟨7613040732625549192123337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81205767814672524715982261 7613040732625549192123337)
        ·
          refine ⟨5709780549469161894092503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7613040732625549192123337 5709780549469161894092503)
          ·
            refine ⟨8564670824203742841138755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5709780549469161894092503 8564670824203742841138755)
            ·
              refine ⟨12847006236305614261708133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8564670824203742841138755 12847006236305614261708133)
              ·
                refine ⟨2408813669307302674070275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12847006236305614261708133 2408813669307302674070275)
                ·
                  refine ⟨3613220503960954011105413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2408813669307302674070275 3613220503960954011105413)
                  ·
                    refine ⟨677478844492678877082265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3613220503960954011105413 677478844492678877082265)
                    ·
                      refine ⟨508109133369509157811699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 677478844492678877082265 508109133369509157811699)
                      ·
                        rfl

theorem cell23_989539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 4, 2].length) (baseStart_989539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989539 prefixEnd_989539 := by exact prefixLift 989539
  have htrace : WordTrace (prefixWord ++ tailWord_989539) baseStart_989539 baseEnd_989539 := by
    simpa [prefixWord, tailWord_989539, baseEnd_989539] using wordTrace_append hprefix tailTrace_989539
  have hstable : (prefixWord ++ tailWord_989539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989539).length < 2 ^ (prefixWord ++ tailWord_989539).sum := by decide
  have hdescent : baseEnd_989539 < baseStart_989539 := by decide
  rcases family_descends (prefixWord ++ tailWord_989539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989543 : List Nat := [1, 1, 5, 1, 3, 1, 4, 1, 1, 3, 2]
def baseStart_989543 : Nat := 118140960795 + 989543 * 2 ^ 59
def prefixEnd_989543 : Nat := 4983230072969 + 3 ^ 40 * 989543 * 2
def baseEnd_989543 : Nat := 508111187292127142161681

theorem tailTrace_989543 : CollatzResearch.WordTrace tailWord_989543 prefixEnd_989543 508111187292127142161681 := by
  unfold tailWord_989543
  simp only [CollatzResearch.WordTrace]
  refine ⟨36091598254062186334693283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24061065502708124223128855 36091598254062186334693283)
  ·
    refine ⟨54137397381093279502039925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36091598254062186334693283 54137397381093279502039925)
    ·
      refine ⟨5075381004477494953316243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54137397381093279502039925 5075381004477494953316243)
      ·
        refine ⟨7613071506716242429974365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5075381004477494953316243 7613071506716242429974365)
        ·
          refine ⟨2854901815018590911240387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7613071506716242429974365 2854901815018590911240387)
          ·
            refine ⟨4282352722527886366860581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2854901815018590911240387 4282352722527886366860581)
            ·
              refine ⟨802941135473978693786359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4282352722527886366860581 802941135473978693786359)
              ·
                refine ⟨1204411703210968040679539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 802941135473978693786359 1204411703210968040679539)
                ·
                  refine ⟨1806617554816452061019309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1204411703210968040679539 1806617554816452061019309)
                  ·
                    refine ⟨677481583056169522882241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1806617554816452061019309 677481583056169522882241)
                    ·
                      refine ⟨508111187292127142161681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 677481583056169522882241 508111187292127142161681)
                      ·
                        rfl

theorem cell23_989543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 1, 1, 3, 2].length) (baseStart_989543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989543 prefixEnd_989543 := by exact prefixLift 989543
  have htrace : WordTrace (prefixWord ++ tailWord_989543) baseStart_989543 baseEnd_989543 := by
    simpa [prefixWord, tailWord_989543, baseEnd_989543] using wordTrace_append hprefix tailTrace_989543
  have hstable : (prefixWord ++ tailWord_989543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989543).length < 2 ^ (prefixWord ++ tailWord_989543).sum := by decide
  have hdescent : baseEnd_989543 < baseStart_989543 := by decide
  rcases family_descends (prefixWord ++ tailWord_989543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989545 : List Nat := [1, 2, 1, 1, 1, 3, 3, 2, 9]
def baseStart_989545 : Nat := 118140960795 + 989545 * 2 ^ 59
def prefixEnd_989545 : Nat := 4983230072969 + 3 ^ 40 * 989545 * 2
def baseEnd_989545 : Nat := 56456912694826237148519

theorem tailTrace_989545 : CollatzResearch.WordTrace tailWord_989545 prefixEnd_989545 56456912694826237148519 := by
  unfold tailWord_989545
  simp only [CollatzResearch.WordTrace]
  refine ⟨36091671200054940676266089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24061114133369960450844059 36091671200054940676266089)
  ·
    refine ⟨27068753400041205507199567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36091671200054940676266089 27068753400041205507199567)
    ·
      refine ⟨40603130100061808260799351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27068753400041205507199567 40603130100061808260799351)
      ·
        refine ⟨60904695150092712391199027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40603130100061808260799351 60904695150092712391199027)
        ·
          refine ⟨91357042725139068586798541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60904695150092712391199027 91357042725139068586798541)
          ·
            refine ⟨34258891021927150720049453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91357042725139068586798541 34258891021927150720049453)
            ·
              refine ⟨12847084133222681520018545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34258891021927150720049453 12847084133222681520018545)
              ·
                refine ⟨9635313099917011140013909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12847084133222681520018545 9635313099917011140013909)
                ·
                  refine ⟨56456912694826237148519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 9635313099917011140013909 56456912694826237148519)
                  ·
                    rfl

theorem cell23_989545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 9].length) (baseStart_989545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989545 prefixEnd_989545 := by exact prefixLift 989545
  have htrace : WordTrace (prefixWord ++ tailWord_989545) baseStart_989545 baseEnd_989545 := by
    simpa [prefixWord, tailWord_989545, baseEnd_989545] using wordTrace_append hprefix tailTrace_989545
  have hstable : (prefixWord ++ tailWord_989545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989545).length < 2 ^ (prefixWord ++ tailWord_989545).sum := by decide
  have hdescent : baseEnd_989545 < baseStart_989545 := by decide
  rcases family_descends (prefixWord ++ tailWord_989545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989552 : List Nat := [2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 4]
def baseStart_989552 : Nat := 118140960795 + 989552 * 2 ^ 59
def prefixEnd_989552 : Nat := 4983230072969 + 3 ^ 40 * 989552 * 2
def baseEnd_989552 : Nat := 508115808618017606949139

theorem tailTrace_989552 : CollatzResearch.WordTrace tailWord_989552 prefixEnd_989552 508115808618017606949139 := by
  unfold tailWord_989552
  simp only [CollatzResearch.WordTrace]
  refine ⟨18045963255514790435885455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24061284340686387247847273 18045963255514790435885455)
  ·
    refine ⟨27068944883272185653828183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18045963255514790435885455 27068944883272185653828183)
    ·
      refine ⟨40603417324908278480742275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27068944883272185653828183 40603417324908278480742275)
      ·
        refine ⟨60905125987362417721113413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40603417324908278480742275 60905125987362417721113413)
        ·
          refine ⟨11419711122630453322708765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60905125987362417721113413 11419711122630453322708765)
          ·
            refine ⟨4282391670986419996015787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11419711122630453322708765 4282391670986419996015787)
            ·
              refine ⟨6423587506479629994023681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4282391670986419996015787 6423587506479629994023681)
              ·
                refine ⟨4817690629859722495517761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6423587506479629994023681 4817690629859722495517761)
                ·
                  refine ⟨3613267972394791871638321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4817690629859722495517761 3613267972394791871638321)
                  ·
                    refine ⟨2709950979296093903728741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3613267972394791871638321 2709950979296093903728741)
                    ·
                      refine ⟨508115808618017606949139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2709950979296093903728741 508115808618017606949139)
                      ·
                        rfl

theorem cell23_989552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 4].length) (baseStart_989552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989552 prefixEnd_989552 := by exact prefixLift 989552
  have htrace : WordTrace (prefixWord ++ tailWord_989552) baseStart_989552 baseEnd_989552 := by
    simpa [prefixWord, tailWord_989552, baseEnd_989552] using wordTrace_append hprefix tailTrace_989552
  have hstable : (prefixWord ++ tailWord_989552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989552).length < 2 ^ (prefixWord ++ tailWord_989552).sum := by decide
  have hdescent : baseEnd_989552 < baseStart_989552 := by decide
  rcases family_descends (prefixWord ++ tailWord_989552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989555 : List Nat := [1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 7]
def baseStart_989555 : Nat := 118140960795 + 989555 * 2 ^ 59
def prefixEnd_989555 : Nat := 4983230072969 + 3 ^ 40 * 989555 * 2
def baseEnd_989555 : Nat := 508117349059981095211625

theorem tailTrace_989555 : CollatzResearch.WordTrace tailWord_989555 prefixEnd_989555 508117349059981095211625 := by
  unfold tailWord_989555
  simp only [CollatzResearch.WordTrace]
  refine ⟨36092035930018712384130119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24061357286679141589420079 36092035930018712384130119)
  ·
    refine ⟨54138053895028068576195179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36092035930018712384130119 54138053895028068576195179)
    ·
      refine ⟨81207080842542102864292769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54138053895028068576195179 81207080842542102864292769)
      ·
        refine ⟨60905310631906577148219577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81207080842542102864292769 60905310631906577148219577)
        ·
          refine ⟨45678982973929932861164683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60905310631906577148219577 45678982973929932861164683)
          ·
            refine ⟨68518474460894899291747025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45678982973929932861164683 68518474460894899291747025)
            ·
              refine ⟨51388855845671174468810269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68518474460894899291747025 51388855845671174468810269)
              ·
                refine ⟨19270820942126690425803851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51388855845671174468810269 19270820942126690425803851)
                ·
                  refine ⟨28906231413190035638705777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19270820942126690425803851 28906231413190035638705777)
                  ·
                    refine ⟨21679673559892526729029333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28906231413190035638705777 21679673559892526729029333)
                    ·
                      refine ⟨508117349059981095211625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 21679673559892526729029333 508117349059981095211625)
                      ·
                        rfl

theorem cell23_989555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 7].length) (baseStart_989555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989555 prefixEnd_989555 := by exact prefixLift 989555
  have htrace : WordTrace (prefixWord ++ tailWord_989555) baseStart_989555 baseEnd_989555 := by
    simpa [prefixWord, tailWord_989555, baseEnd_989555] using wordTrace_append hprefix tailTrace_989555
  have hstable : (prefixWord ++ tailWord_989555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989555).length < 2 ^ (prefixWord ++ tailWord_989555).sum := by decide
  have hdescent : baseEnd_989555 < baseStart_989555 := by decide
  rcases family_descends (prefixWord ++ tailWord_989555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989569 : List Nat := [1, 2, 4, 3, 1, 1, 2, 1, 2, 2, 4]
def baseStart_989569 : Nat := 118140960795 + 989569 * 2 ^ 59
def prefixEnd_989569 : Nat := 4983230072969 + 3 ^ 40 * 989569 * 2
def baseEnd_989569 : Nat := 508124537789144040436561

theorem tailTrace_989569 : CollatzResearch.WordTrace tailWord_989569 prefixEnd_989569 508124537789144040436561 := by
  unfold tailWord_989569
  simp only [CollatzResearch.WordTrace]
  refine ⟨36092546551967992775139761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24061697701311995183426507 36092546551967992775139761)
  ·
    refine ⟨27069409913975994581354821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36092546551967992775139761 27069409913975994581354821)
    ·
      refine ⟨5075514358870498984004029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27069409913975994581354821 5075514358870498984004029)
      ·
        refine ⟨1903317884576437119001511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5075514358870498984004029 1903317884576437119001511)
        ·
          refine ⟨2854976826864655678502267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1903317884576437119001511 2854976826864655678502267)
          ·
            refine ⟨4282465240296983517753401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2854976826864655678502267 4282465240296983517753401)
            ·
              refine ⟨3211848930222737638315051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4282465240296983517753401 3211848930222737638315051)
              ·
                refine ⟨4817773395334106457472577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3211848930222737638315051 4817773395334106457472577)
                ·
                  refine ⟨3613330046500579843104433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4817773395334106457472577 3613330046500579843104433)
                  ·
                    refine ⟨2709997534875434882328325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3613330046500579843104433 2709997534875434882328325)
                    ·
                      refine ⟨508124537789144040436561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2709997534875434882328325 508124537789144040436561)
                      ·
                        rfl

theorem cell23_989569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_989569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989569 prefixEnd_989569 := by exact prefixLift 989569
  have htrace : WordTrace (prefixWord ++ tailWord_989569) baseStart_989569 baseEnd_989569 := by
    simpa [prefixWord, tailWord_989569, baseEnd_989569] using wordTrace_append hprefix tailTrace_989569
  have hstable : (prefixWord ++ tailWord_989569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989569).length < 2 ^ (prefixWord ++ tailWord_989569).sum := by decide
  have hdescent : baseEnd_989569 < baseStart_989569 := by decide
  rcases family_descends (prefixWord ++ tailWord_989569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989613 : List Nat := [1, 5, 2, 2, 3, 1, 1, 1, 7]
def baseStart_989613 : Nat := 118140960795 + 989613 * 2 ^ 59
def prefixEnd_989613 : Nat := 4983230072969 + 3 ^ 40 * 989613 * 2
def baseEnd_989613 : Nat := 56460792326437985365151

theorem tailTrace_989613 : CollatzResearch.WordTrace tailWord_989613 prefixEnd_989613 56460792326437985365151 := by
  unfold tailWord_989613
  simp only [CollatzResearch.WordTrace]
  refine ⟨36094151363808588289741493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24062767575872392193160995 36094151363808588289741493)
  ·
    refine ⟨3383826690357055152163265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36094151363808588289741493 3383826690357055152163265)
    ·
      refine ⟨2537870017767791364122449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3383826690357055152163265 2537870017767791364122449)
      ·
        refine ⟨1903402513325843523091837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2537870017767791364122449 1903402513325843523091837)
        ·
          refine ⟨713775942497191321159439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1903402513325843523091837 713775942497191321159439)
          ·
            refine ⟨1070663913745786981739159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 713775942497191321159439 1070663913745786981739159)
            ·
              refine ⟨1605995870618680472608739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1070663913745786981739159 1605995870618680472608739)
              ·
                refine ⟨2408993805928020708913109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1605995870618680472608739 2408993805928020708913109)
                ·
                  refine ⟨56460792326437985365151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2408993805928020708913109 56460792326437985365151)
                  ·
                    rfl

theorem cell23_989613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 7].length) (baseStart_989613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989613 prefixEnd_989613 := by exact prefixLift 989613
  have htrace : WordTrace (prefixWord ++ tailWord_989613) baseStart_989613 baseEnd_989613 := by
    simpa [prefixWord, tailWord_989613, baseEnd_989613] using wordTrace_append hprefix tailTrace_989613
  have hstable : (prefixWord ++ tailWord_989613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989613).length < 2 ^ (prefixWord ++ tailWord_989613).sum := by decide
  have hdescent : baseEnd_989613 < baseStart_989613 := by decide
  rcases family_descends (prefixWord ++ tailWord_989613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989656 : List Nat := [2, 1, 2, 2, 2, 1, 1, 7, 1, 4]
def baseStart_989656 : Nat := 118140960795 + 989656 * 2 ^ 59
def prefixEnd_989656 : Nat := 4983230072969 + 3 ^ 40 * 989656 * 2
def baseEnd_989656 : Nat := 169389736868695066682887

theorem tailTrace_989656 : CollatzResearch.WordTrace tailWord_989656 prefixEnd_989656 169389736868695066682887 := by
  unfold tailWord_989656
  simp only [CollatzResearch.WordTrace]
  refine ⟨18047859851326403316778411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24063813135101871089037881 18047859851326403316778411)
  ·
    refine ⟨27071789776989604975167617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18047859851326403316778411 27071789776989604975167617)
    ·
      refine ⟨20303842332742203731375713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27071789776989604975167617 20303842332742203731375713)
      ·
        refine ⟨15227881749556652798531785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20303842332742203731375713 15227881749556652798531785)
        ·
          refine ⟨11420911312167489598898839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15227881749556652798531785 11420911312167489598898839)
          ·
            refine ⟨17131366968251234398348259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11420911312167489598898839 17131366968251234398348259)
            ·
              refine ⟨25697050452376851597522389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17131366968251234398348259 25697050452376851597522389)
              ·
                refine ⟨602274619977582459316931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 25697050452376851597522389 602274619977582459316931)
                ·
                  refine ⟨903411929966373688975397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 602274619977582459316931 903411929966373688975397)
                  ·
                    refine ⟨169389736868695066682887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 903411929966373688975397 169389736868695066682887)
                    ·
                      rfl

theorem cell23_989656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 7, 1, 4].length) (baseStart_989656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989656 prefixEnd_989656 := by exact prefixLift 989656
  have htrace : WordTrace (prefixWord ++ tailWord_989656) baseStart_989656 baseEnd_989656 := by
    simpa [prefixWord, tailWord_989656, baseEnd_989656] using wordTrace_append hprefix tailTrace_989656
  have hstable : (prefixWord ++ tailWord_989656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989656).length < 2 ^ (prefixWord ++ tailWord_989656).sum := by decide
  have hdescent : baseEnd_989656 < baseStart_989656 := by decide
  rcases family_descends (prefixWord ++ tailWord_989656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989692 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 1, 3, 7]
def baseStart_989692 : Nat := 118140960795 + 989692 * 2 ^ 59
def prefixEnd_989692 : Nat := 4983230072969 + 3 ^ 40 * 989692 * 2
def baseEnd_989692 : Nat := 508187695909647059198495

theorem tailTrace_989692 : CollatzResearch.WordTrace tailWord_989692 prefixEnd_989692 508187695909647059198495 := by
  unfold tailWord_989692
  simp only [CollatzResearch.WordTrace]
  refine ⟨18048516365261192390933665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24064688487014923187911553 18048516365261192390933665)
  ·
    refine ⟨13536387273945894293200249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18048516365261192390933665 13536387273945894293200249)
    ·
      refine ⟨10152290455459420719900187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13536387273945894293200249 10152290455459420719900187)
      ·
        refine ⟨15228435683189131079850281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10152290455459420719900187 15228435683189131079850281)
        ·
          refine ⟨11421326762391848309887711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15228435683189131079850281 11421326762391848309887711)
          ·
            refine ⟨17131990143587772464831567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11421326762391848309887711 17131990143587772464831567)
            ·
              refine ⟨25697985215381658697247351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17131990143587772464831567 25697985215381658697247351)
              ·
                refine ⟨38546977823072488045871027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25697985215381658697247351 38546977823072488045871027)
                ·
                  refine ⟨57820466734608732068806541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38546977823072488045871027 57820466734608732068806541)
                  ·
                    refine ⟨21682675025478274525802453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57820466734608732068806541 21682675025478274525802453)
                    ·
                      refine ⟨508187695909647059198495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 21682675025478274525802453 508187695909647059198495)
                      ·
                        rfl

theorem cell23_989692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_989692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989692 prefixEnd_989692 := by exact prefixLift 989692
  have htrace : WordTrace (prefixWord ++ tailWord_989692) baseStart_989692 baseEnd_989692 := by
    simpa [prefixWord, tailWord_989692, baseEnd_989692] using wordTrace_append hprefix tailTrace_989692
  have hstable : (prefixWord ++ tailWord_989692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989692).length < 2 ^ (prefixWord ++ tailWord_989692).sum := by decide
  have hdescent : baseEnd_989692 < baseStart_989692 := by decide
  rcases family_descends (prefixWord ++ tailWord_989692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989699 : List Nat := [1, 1, 1, 3, 2, 1, 4, 4, 1, 5]
def baseStart_989699 : Nat := 118140960795 + 989699 * 2 ^ 59
def prefixEnd_989699 : Nat := 4983230072969 + 3 ^ 40 * 989699 * 2
def baseEnd_989699 : Nat := 169397096758076177270321

theorem tailTrace_989699 : CollatzResearch.WordTrace tailWord_989699 prefixEnd_989699 169397096758076177270321 := by
  unfold tailWord_989699
  simp only [CollatzResearch.WordTrace]
  refine ⟨36097288041497024977372151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24064858694331349984914767 36097288041497024977372151)
  ·
    refine ⟨54145932062245537466058227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36097288041497024977372151 54145932062245537466058227)
    ·
      refine ⟨81218898093368306199087341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54145932062245537466058227 81218898093368306199087341)
      ·
        refine ⟨30457086785013114824657753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81218898093368306199087341 30457086785013114824657753)
        ·
          refine ⟨22842815088759836118493315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30457086785013114824657753 22842815088759836118493315)
          ·
            refine ⟨34264222633139754177739973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22842815088759836118493315 34264222633139754177739973)
            ·
              refine ⟨6424541743713703908326245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34264222633139754177739973 6424541743713703908326245)
              ·
                refine ⟨1204601576946319482811171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6424541743713703908326245 1204601576946319482811171)
                ·
                  refine ⟨1806902365419479224216757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1204601576946319482811171 1806902365419479224216757)
                  ·
                    refine ⟨169397096758076177270321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1806902365419479224216757 169397096758076177270321)
                    ·
                      rfl

theorem cell23_989699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 4, 1, 5].length) (baseStart_989699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989699 prefixEnd_989699 := by exact prefixLift 989699
  have htrace : WordTrace (prefixWord ++ tailWord_989699) baseStart_989699 baseEnd_989699 := by
    simpa [prefixWord, tailWord_989699, baseEnd_989699] using wordTrace_append hprefix tailTrace_989699
  have hstable : (prefixWord ++ tailWord_989699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989699).length < 2 ^ (prefixWord ++ tailWord_989699).sum := by decide
  have hdescent : baseEnd_989699 < baseStart_989699 := by decide
  rcases family_descends (prefixWord ++ tailWord_989699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989706 : List Nat := [3, 1, 2, 2, 2, 1, 3, 1, 1, 5, 2]
def baseStart_989706 : Nat := 118140960795 + 989706 * 2 ^ 59
def prefixEnd_989706 : Nat := 4983230072969 + 3 ^ 40 * 989706 * 2
def baseEnd_989706 : Nat := 508194884638810004423431

theorem tailTrace_989706 : CollatzResearch.WordTrace tailWord_989706 prefixEnd_989706 508194884638810004423431 := by
  unfold tailWord_989706
  simp only [CollatzResearch.WordTrace]
  refine ⟨9024385838117916293219243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24065028901647776781917981 9024385838117916293219243)
  ·
    refine ⟨13536578757176874439828865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9024385838117916293219243 13536578757176874439828865)
    ·
      refine ⟨10152434067882655829871649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13536578757176874439828865 10152434067882655829871649)
      ·
        refine ⟨7614325550911991872403737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10152434067882655829871649 7614325550911991872403737)
        ·
          refine ⟨5710744163183993904302803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7614325550911991872403737 5710744163183993904302803)
          ·
            refine ⟨8566116244775990856454205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5710744163183993904302803 8566116244775990856454205)
            ·
              refine ⟨3212293591790996571170327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8566116244775990856454205 3212293591790996571170327)
              ·
                refine ⟨4818440387686494856755491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3212293591790996571170327 4818440387686494856755491)
                ·
                  refine ⟨7227660581529742285133237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4818440387686494856755491 7227660581529742285133237)
                  ·
                    refine ⟨677593179518413339231241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7227660581529742285133237 677593179518413339231241)
                    ·
                      refine ⟨508194884638810004423431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 677593179518413339231241 508194884638810004423431)
                      ·
                        rfl

theorem cell23_989706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 1, 5, 2].length) (baseStart_989706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989706 prefixEnd_989706 := by exact prefixLift 989706
  have htrace : WordTrace (prefixWord ++ tailWord_989706) baseStart_989706 baseEnd_989706 := by
    simpa [prefixWord, tailWord_989706, baseEnd_989706] using wordTrace_append hprefix tailTrace_989706
  have hstable : (prefixWord ++ tailWord_989706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989706).length < 2 ^ (prefixWord ++ tailWord_989706).sum := by decide
  have hdescent : baseEnd_989706 < baseStart_989706 := by decide
  rcases family_descends (prefixWord ++ tailWord_989706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989712 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 7, 6]
def baseStart_989712 : Nat := 118140960795 + 989712 * 2 ^ 59
def prefixEnd_989712 : Nat := 4983230072969 + 3 ^ 40 * 989712 * 2
def baseEnd_989712 : Nat := 169399321840912326982801

theorem tailTrace_989712 : CollatzResearch.WordTrace tailWord_989712 prefixEnd_989712 169399321840912326982801 := by
  unfold tailWord_989712
  simp only [CollatzResearch.WordTrace]
  refine ⟨18048881095224964098797695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24065174793633285465063593 18048881095224964098797695)
  ·
    refine ⟨27073321642837446148196543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18048881095224964098797695 27073321642837446148196543)
    ·
      refine ⟨40609982464256169222294815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27073321642837446148196543 40609982464256169222294815)
      ·
        refine ⟨60914973696384253833442223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40609982464256169222294815 60914973696384253833442223)
        ·
          refine ⟨91372460544576380750163335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60914973696384253833442223 91372460544576380750163335)
          ·
            refine ⟨137058690816864571125245003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91372460544576380750163335 137058690816864571125245003)
            ·
              refine ⟨205588036225296856687867505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137058690816864571125245003 205588036225296856687867505)
              ·
                refine ⟨154191027168972642515900629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205588036225296856687867505 154191027168972642515900629)
                ·
                  refine ⟨3613852199272796308966421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 154191027168972642515900629 3613852199272796308966421)
                  ·
                    refine ⟨169399321840912326982801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3613852199272796308966421 169399321840912326982801)
                    ·
                      rfl

theorem cell23_989712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 7, 6].length) (baseStart_989712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989712 prefixEnd_989712 := by exact prefixLift 989712
  have htrace : WordTrace (prefixWord ++ tailWord_989712) baseStart_989712 baseEnd_989712 := by
    simpa [prefixWord, tailWord_989712, baseEnd_989712] using wordTrace_append hprefix tailTrace_989712
  have hstable : (prefixWord ++ tailWord_989712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989712).length < 2 ^ (prefixWord ++ tailWord_989712).sum := by decide
  have hdescent : baseEnd_989712 < baseStart_989712 := by decide
  rcases family_descends (prefixWord ++ tailWord_989712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989739 : List Nat := [1, 1, 1, 1, 2, 1, 3, 3, 5, 2, 3]
def baseStart_989739 : Nat := 118140960795 + 989739 * 2 ^ 59
def prefixEnd_989739 : Nat := 4983230072969 + 3 ^ 40 * 989739 * 2
def baseEnd_989739 : Nat := 508211829500408375310779

theorem tailTrace_989739 : CollatzResearch.WordTrace tailWord_989739 prefixEnd_989739 508211829500408375310779 := by
  unfold tailWord_989739
  simp only [CollatzResearch.WordTrace]
  refine ⟨36098746961352111808828271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24065831307568074539218847 36098746961352111808828271)
  ·
    refine ⟨54148120442028167713242407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36098746961352111808828271 54148120442028167713242407)
    ·
      refine ⟨81222180663042251569863611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54148120442028167713242407 81222180663042251569863611)
      ·
        refine ⟨121833270994563377354795417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81222180663042251569863611 121833270994563377354795417)
        ·
          refine ⟨91374953245922533016096563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121833270994563377354795417 91374953245922533016096563)
          ·
            refine ⟨137062429868883799524144845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91374953245922533016096563 137062429868883799524144845)
            ·
              refine ⟨51398411200831424821554317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137062429868883799524144845 51398411200831424821554317)
              ·
                refine ⟨19274404200311784308082869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51398411200831424821554317 19274404200311784308082869)
                ·
                  refine ⟨1806975393779229778882769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19274404200311784308082869 1806975393779229778882769)
                  ·
                    refine ⟨1355231545334422334162077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1806975393779229778882769 1355231545334422334162077)
                    ·
                      refine ⟨508211829500408375310779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1355231545334422334162077 508211829500408375310779)
                      ·
                        rfl

theorem cell23_989739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 5, 2, 3].length) (baseStart_989739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989739 prefixEnd_989739 := by exact prefixLift 989739
  have htrace : WordTrace (prefixWord ++ tailWord_989739) baseStart_989739 baseEnd_989739 := by
    simpa [prefixWord, tailWord_989739, baseEnd_989739] using wordTrace_append hprefix tailTrace_989739
  have hstable : (prefixWord ++ tailWord_989739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989739).length < 2 ^ (prefixWord ++ tailWord_989739).sum := by decide
  have hdescent : baseEnd_989739 < baseStart_989739 := by decide
  rcases family_descends (prefixWord ++ tailWord_989739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989746 : List Nat := [3, 2, 1, 1, 2, 1, 2, 5, 2, 4]
def baseStart_989746 : Nat := 118140960795 + 989746 * 2 ^ 59
def prefixEnd_989746 : Nat := 4983230072969 + 3 ^ 40 * 989746 * 2
def baseEnd_989746 : Nat := 169405141288329949307749

theorem tailTrace_989746 : CollatzResearch.WordTrace tailWord_989746 prefixEnd_989746 169405141288329949307749 := by
  unfold tailWord_989746
  simp only [CollatzResearch.WordTrace]
  refine ⟨9024750568081688001083273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24066001514884501336222061 9024750568081688001083273)
  ·
    refine ⟨6768562926061266000812455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9024750568081688001083273 6768562926061266000812455)
    ·
      refine ⟨10152844389091899001218683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6768562926061266000812455 10152844389091899001218683)
      ·
        refine ⟨15229266583637848501828025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10152844389091899001218683 15229266583637848501828025)
        ·
          refine ⟨11421949937728386376371019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15229266583637848501828025 11421949937728386376371019)
          ·
            refine ⟨17132924906592579564556529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11421949937728386376371019 17132924906592579564556529)
            ·
              refine ⟨12849693679944434673417397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17132924906592579564556529 12849693679944434673417397)
              ·
                refine ⟨1204658782494790750632881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12849693679944434673417397 1204658782494790750632881)
                ·
                  refine ⟨903494086871093062974661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1204658782494790750632881 903494086871093062974661)
                  ·
                    refine ⟨169405141288329949307749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 903494086871093062974661 169405141288329949307749)
                    ·
                      rfl

theorem cell23_989746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 5, 2, 4].length) (baseStart_989746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989746 prefixEnd_989746 := by exact prefixLift 989746
  have htrace : WordTrace (prefixWord ++ tailWord_989746) baseStart_989746 baseEnd_989746 := by
    simpa [prefixWord, tailWord_989746, baseEnd_989746] using wordTrace_append hprefix tailTrace_989746
  have hstable : (prefixWord ++ tailWord_989746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989746).length < 2 ^ (prefixWord ++ tailWord_989746).sum := by decide
  have hdescent : baseEnd_989746 < baseStart_989746 := by decide
  rcases family_descends (prefixWord ++ tailWord_989746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989749 : List Nat := [1, 3, 3, 1, 1, 2, 3, 1, 1, 1, 6]
def baseStart_989749 : Nat := 118140960795 + 989749 * 2 ^ 59
def prefixEnd_989749 : Nat := 4983230072969 + 3 ^ 40 * 989749 * 2
def baseEnd_989749 : Nat := 508216964306953336185733

theorem tailTrace_989749 : CollatzResearch.WordTrace tailWord_989749 prefixEnd_989749 508216964306953336185733 := by
  unfold tailWord_989749
  simp only [CollatzResearch.WordTrace]
  refine ⟨36099111691315883516692301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24066074460877255677794867 36099111691315883516692301)
  ·
    refine ⟨13537166884243456318759613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36099111691315883516692301 13537166884243456318759613)
    ·
      refine ⟨5076437581591296119534855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13537166884243456318759613 5076437581591296119534855)
      ·
        refine ⟨7614656372386944179302283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5076437581591296119534855 7614656372386944179302283)
        ·
          refine ⟨11421984558580416268953425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7614656372386944179302283 11421984558580416268953425)
          ·
            refine ⟨8566488418935312201715069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11421984558580416268953425 8566488418935312201715069)
            ·
              refine ⟨3212433157100742075643151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8566488418935312201715069 3212433157100742075643151)
              ·
                refine ⟨4818649735651113113464727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3212433157100742075643151 4818649735651113113464727)
                ·
                  refine ⟨7227974603476669670197091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4818649735651113113464727 7227974603476669670197091)
                  ·
                    refine ⟨10841961905215004505295637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7227974603476669670197091 10841961905215004505295637)
                    ·
                      refine ⟨508216964306953336185733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10841961905215004505295637 508216964306953336185733)
                      ·
                        rfl

theorem cell23_989749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_989749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989749 prefixEnd_989749 := by exact prefixLift 989749
  have htrace : WordTrace (prefixWord ++ tailWord_989749) baseStart_989749 baseEnd_989749 := by
    simpa [prefixWord, tailWord_989749, baseEnd_989749] using wordTrace_append hprefix tailTrace_989749
  have hstable : (prefixWord ++ tailWord_989749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989749).length < 2 ^ (prefixWord ++ tailWord_989749).sum := by decide
  have hdescent : baseEnd_989749 < baseStart_989749 := by decide
  rcases family_descends (prefixWord ++ tailWord_989749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989753 : List Nat := [1, 2, 1, 5, 1, 1, 1, 4, 3, 2, 2]
def baseStart_989753 : Nat := 118140960795 + 989753 * 2 ^ 59
def prefixEnd_989753 : Nat := 4983230072969 + 3 ^ 40 * 989753 * 2
def baseEnd_989753 : Nat := 508219018229571320535715

theorem tailTrace_989753 : CollatzResearch.WordTrace tailWord_989753 prefixEnd_989753 508219018229571320535715 := by
  unfold tailWord_989753
  simp only [CollatzResearch.WordTrace]
  refine ⟨36099257583301392199837913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24066171722200928133225275 36099257583301392199837913)
  ·
    refine ⟨27074443187476044149878435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36099257583301392199837913 27074443187476044149878435)
    ·
      refine ⟨40611664781214066224817653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27074443187476044149878435 40611664781214066224817653)
      ·
        refine ⟨3807343573238818708576655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40611664781214066224817653 3807343573238818708576655)
        ·
          refine ⟨5711015359858228062864983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3807343573238818708576655 5711015359858228062864983)
          ·
            refine ⟨8566523039787342094297475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5711015359858228062864983 8566523039787342094297475)
            ·
              refine ⟨12849784559681013141446213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8566523039787342094297475 12849784559681013141446213)
              ·
                refine ⟨2409334604940189964021165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12849784559681013141446213 2409334604940189964021165)
                ·
                  refine ⟨903500476852571236507937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2409334604940189964021165 903500476852571236507937)
                  ·
                    refine ⟨677625357639428427380953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 903500476852571236507937 677625357639428427380953)
                    ·
                      refine ⟨508219018229571320535715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 677625357639428427380953 508219018229571320535715)
                      ·
                        rfl

theorem cell23_989753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_989753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989753 prefixEnd_989753 := by exact prefixLift 989753
  have htrace : WordTrace (prefixWord ++ tailWord_989753) baseStart_989753 baseEnd_989753 := by
    simpa [prefixWord, tailWord_989753, baseEnd_989753] using wordTrace_append hprefix tailTrace_989753
  have hstable : (prefixWord ++ tailWord_989753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989753).length < 2 ^ (prefixWord ++ tailWord_989753).sum := by decide
  have hdescent : baseEnd_989753 < baseStart_989753 := by decide
  rcases family_descends (prefixWord ++ tailWord_989753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989773 : List Nat := [1, 6, 1, 1, 2, 2, 2, 1, 1, 1, 5]
def baseStart_989773 : Nat := 118140960795 + 989773 * 2 ^ 59
def prefixEnd_989773 : Nat := 4983230072969 + 3 ^ 40 * 989773 * 2
def baseEnd_989773 : Nat := 508229287842661242285623

theorem tailTrace_989773 : CollatzResearch.WordTrace tailWord_989773 prefixEnd_989773 508229287842661242285623 := by
  unfold tailWord_989773
  simp only [CollatzResearch.WordTrace]
  refine ⟨36099987043228935615565973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24066658028819290410377315 36099987043228935615565973)
  ·
    refine ⟨1692186892651356356979655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 36099987043228935615565973 1692186892651356356979655)
    ·
      refine ⟨2538280338977034535469483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1692186892651356356979655 2538280338977034535469483)
      ·
        refine ⟨3807420508465551803204225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2538280338977034535469483 3807420508465551803204225)
        ·
          refine ⟨2855565381349163852403169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3807420508465551803204225 2855565381349163852403169)
          ·
            refine ⟨2141674036011872889302377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2855565381349163852403169 2141674036011872889302377)
            ·
              refine ⟨1606255527008904666976783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2141674036011872889302377 1606255527008904666976783)
              ·
                refine ⟨2409383290513357000465175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1606255527008904666976783 2409383290513357000465175)
                ·
                  refine ⟨3614074935770035500697763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2409383290513357000465175 3614074935770035500697763)
                  ·
                    refine ⟨5421112403655053251046645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3614074935770035500697763 5421112403655053251046645)
                    ·
                      refine ⟨508229287842661242285623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5421112403655053251046645 508229287842661242285623)
                      ·
                        rfl

theorem cell23_989773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_989773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989773 prefixEnd_989773 := by exact prefixLift 989773
  have htrace : WordTrace (prefixWord ++ tailWord_989773) baseStart_989773 baseEnd_989773 := by
    simpa [prefixWord, tailWord_989773, baseEnd_989773] using wordTrace_append hprefix tailTrace_989773
  have hstable : (prefixWord ++ tailWord_989773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989773).length < 2 ^ (prefixWord ++ tailWord_989773).sum := by decide
  have hdescent : baseEnd_989773 < baseStart_989773 := by decide
  rcases family_descends (prefixWord ++ tailWord_989773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989797 : List Nat := [1, 3, 1, 3, 5, 1, 2, 1, 2, 4]
def baseStart_989797 : Nat := 118140960795 + 989797 * 2 ^ 59
def prefixEnd_989797 : Nat := 4983230072969 + 3 ^ 40 * 989797 * 2
def baseEnd_989797 : Nat := 169413870459456382795171

theorem tailTrace_989797 : CollatzResearch.WordTrace tailWord_989797 prefixEnd_989797 169413870459456382795171 := by
  unfold tailWord_989797
  simp only [CollatzResearch.WordTrace]
  refine ⟨36100862395141987714439645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24067241596761325142959763 36100862395141987714439645)
  ·
    refine ⟨13537823398178245392914867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36100862395141987714439645 13537823398178245392914867)
    ·
      refine ⟨20306735097267368089372301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13537823398178245392914867 20306735097267368089372301)
      ·
        refine ⟨7615025661475263033514613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20306735097267368089372301 7615025661475263033514613)
        ·
          refine ⟨713908655763305909391995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7615025661475263033514613 713908655763305909391995)
          ·
            refine ⟨1070862983644958864087993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 713908655763305909391995 1070862983644958864087993)
            ·
              refine ⟨803147237733719148065995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1070862983644958864087993 803147237733719148065995)
              ·
                refine ⟨1204720856600578722098993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 803147237733719148065995 1204720856600578722098993)
                ·
                  refine ⟨903540642450434041574245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1204720856600578722098993 903540642450434041574245)
                  ·
                    refine ⟨169413870459456382795171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 903540642450434041574245 169413870459456382795171)
                    ·
                      rfl

theorem cell23_989797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 1, 2, 4].length) (baseStart_989797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989797 prefixEnd_989797 := by exact prefixLift 989797
  have htrace : WordTrace (prefixWord ++ tailWord_989797) baseStart_989797 baseEnd_989797 := by
    simpa [prefixWord, tailWord_989797, baseEnd_989797] using wordTrace_append hprefix tailTrace_989797
  have hstable : (prefixWord ++ tailWord_989797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989797).length < 2 ^ (prefixWord ++ tailWord_989797).sum := by decide
  have hdescent : baseEnd_989797 < baseStart_989797 := by decide
  rcases family_descends (prefixWord ++ tailWord_989797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989839 : List Nat := [1, 1, 2, 1, 1, 1, 1, 5, 4, 2, 4]
def baseStart_989839 : Nat := 118140960795 + 989839 * 2 ^ 59
def prefixEnd_989839 : Nat := 4983230072969 + 3 ^ 40 * 989839 * 2
def baseEnd_989839 : Nat := 508263177565857984060319

theorem tailTrace_989839 : CollatzResearch.WordTrace tailWord_989839 prefixEnd_989839 508263177565857984060319 := by
  unfold tailWord_989839
  simp only [CollatzResearch.WordTrace]
  refine ⟨36102394260989828887468571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24068262840659885924979047 36102394260989828887468571)
  ·
    refine ⟨54153591391484743331202857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36102394260989828887468571 54153591391484743331202857)
    ·
      refine ⟨40615193543613557498402143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54153591391484743331202857 40615193543613557498402143)
      ·
        refine ⟨60922790315420336247603215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40615193543613557498402143 60922790315420336247603215)
        ·
          refine ⟨91384185473130504371404823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60922790315420336247603215 91384185473130504371404823)
          ·
            refine ⟨137076278209695756557107235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91384185473130504371404823 137076278209695756557107235)
            ·
              refine ⟨205614417314543634835660853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137076278209695756557107235 205614417314543634835660853)
              ·
                refine ⟨19276351623238465765843205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 205614417314543634835660853 19276351623238465765843205)
                ·
                  refine ⟨3614315929357212331095601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19276351623238465765843205 3614315929357212331095601)
                  ·
                    refine ⟨2710736947017909248321701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3614315929357212331095601 2710736947017909248321701)
                    ·
                      refine ⟨508263177565857984060319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2710736947017909248321701 508263177565857984060319)
                      ·
                        rfl

theorem cell23_989839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 2, 4].length) (baseStart_989839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989839 prefixEnd_989839 := by exact prefixLift 989839
  have htrace : WordTrace (prefixWord ++ tailWord_989839) baseStart_989839 baseEnd_989839 := by
    simpa [prefixWord, tailWord_989839, baseEnd_989839] using wordTrace_append hprefix tailTrace_989839
  have hstable : (prefixWord ++ tailWord_989839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989839).length < 2 ^ (prefixWord ++ tailWord_989839).sum := by decide
  have hdescent : baseEnd_989839 < baseStart_989839 := by decide
  rcases family_descends (prefixWord ++ tailWord_989839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989849 : List Nat := [1, 2, 1, 2, 1, 2, 4, 3, 7]
def baseStart_989849 : Nat := 118140960795 + 989849 * 2 ^ 59
def prefixEnd_989849 : Nat := 4983230072969 + 3 ^ 40 * 989849 * 2
def baseEnd_989849 : Nat := 56474256930266993881697

theorem tailTrace_989849 : CollatzResearch.WordTrace tailWord_989849 prefixEnd_989849 56474256930266993881697 := by
  unfold tailWord_989849
  simp only [CollatzResearch.WordTrace]
  refine ⟨36102758990953600595332601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24068505993969067063555067 36102758990953600595332601)
  ·
    refine ⟨27077069243215200446499451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36102758990953600595332601 27077069243215200446499451)
    ·
      refine ⟨40615603864822800669749177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27077069243215200446499451 40615603864822800669749177)
      ·
        refine ⟨30461702898617100502311883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40615603864822800669749177 30461702898617100502311883)
        ·
          refine ⟨45692554347925650753467825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30461702898617100502311883 45692554347925650753467825)
          ·
            refine ⟨34269415760944238065100869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45692554347925650753467825 34269415760944238065100869)
            ·
              refine ⟨6425515455177044637206413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34269415760944238065100869 6425515455177044637206413)
              ·
                refine ⟨2409568295691391738952405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6425515455177044637206413 2409568295691391738952405)
                ·
                  refine ⟨56474256930266993881697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2409568295691391738952405 56474256930266993881697)
                  ·
                    rfl

theorem cell23_989849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 7].length) (baseStart_989849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989849 prefixEnd_989849 := by exact prefixLift 989849
  have htrace : WordTrace (prefixWord ++ tailWord_989849) baseStart_989849 baseEnd_989849 := by
    simpa [prefixWord, tailWord_989849, baseEnd_989849] using wordTrace_append hprefix tailTrace_989849
  have hstable : (prefixWord ++ tailWord_989849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989849).length < 2 ^ (prefixWord ++ tailWord_989849).sum := by decide
  have hdescent : baseEnd_989849 < baseStart_989849 := by decide
  rcases family_descends (prefixWord ++ tailWord_989849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989860 : List Nat := [2, 3, 1, 2, 2, 1, 1, 5, 2, 2, 2]
def baseStart_989860 : Nat := 118140960795 + 989860 * 2 ^ 59
def prefixEnd_989860 : Nat := 4983230072969 + 3 ^ 40 * 989860 * 2
def baseEnd_989860 : Nat := 508273960659602401897723

theorem tailTrace_989860 : CollatzResearch.WordTrace tailWord_989860 prefixEnd_989860 508273960659602401897723 := by
  unfold tailWord_989860
  simp only [CollatzResearch.WordTrace]
  refine ⟨18051580096956874736991517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24068773462609166315988689 18051580096956874736991517)
  ·
    refine ⟨6769342536358828026371819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18051580096956874736991517 6769342536358828026371819)
    ·
      refine ⟨10154013804538242039557729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6769342536358828026371819 10154013804538242039557729)
      ·
        refine ⟨7615510353403681529668297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10154013804538242039557729 7615510353403681529668297)
        ·
          refine ⟨5711632765052761147251223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7615510353403681529668297 5711632765052761147251223)
          ·
            refine ⟨8567449147579141720876835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5711632765052761147251223 8567449147579141720876835)
            ·
              refine ⟨12851173721368712581315253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8567449147579141720876835 12851173721368712581315253)
              ·
                refine ⟨1204797536378316804498305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12851173721368712581315253 1204797536378316804498305)
                ·
                  refine ⟨903598152283737603373729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1204797536378316804498305 903598152283737603373729)
                  ·
                    refine ⟨677698614212803202530297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 903598152283737603373729 677698614212803202530297)
                    ·
                      refine ⟨508273960659602401897723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 677698614212803202530297 508273960659602401897723)
                      ·
                        rfl

theorem cell23_989860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 5, 2, 2, 2].length) (baseStart_989860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989860 prefixEnd_989860 := by exact prefixLift 989860
  have htrace : WordTrace (prefixWord ++ tailWord_989860) baseStart_989860 baseEnd_989860 := by
    simpa [prefixWord, tailWord_989860, baseEnd_989860] using wordTrace_append hprefix tailTrace_989860
  have hstable : (prefixWord ++ tailWord_989860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989860).length < 2 ^ (prefixWord ++ tailWord_989860).sum := by decide
  have hdescent : baseEnd_989860 < baseStart_989860 := by decide
  rcases family_descends (prefixWord ++ tailWord_989860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989933 : List Nat := [1, 5, 1, 2, 1, 1, 2, 3, 2, 1, 4]
def baseStart_989933 : Nat := 118140960795 + 989933 * 2 ^ 59
def prefixEnd_989933 : Nat := 4983230072969 + 3 ^ 40 * 989933 * 2
def baseEnd_989933 : Nat := 508311444747380616284887

theorem tailTrace_989933 : CollatzResearch.WordTrace tailWord_989933 prefixEnd_989933 508311444747380616284887 := by
  unfold tailWord_989933
  simp only [CollatzResearch.WordTrace]
  refine ⟨36105822722649282941390453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24070548481766188627593635 36105822722649282941390453)
  ·
    refine ⟨3384920880248370275755355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36105822722649282941390453 3384920880248370275755355)
    ·
      refine ⟨5077381320372555413633033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3384920880248370275755355 5077381320372555413633033)
      ·
        refine ⟨3808035990279416560224775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5077381320372555413633033 3808035990279416560224775)
        ·
          refine ⟨5712053985419124840337163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3808035990279416560224775 5712053985419124840337163)
          ·
            refine ⟨8568080978128687260505745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5712053985419124840337163 8568080978128687260505745)
            ·
              refine ⟨6426060733596515445379309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8568080978128687260505745 6426060733596515445379309)
              ·
                refine ⟨2409772775098693292017241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6426060733596515445379309 2409772775098693292017241)
                ·
                  refine ⟨1807329581324019969012931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2409772775098693292017241 1807329581324019969012931)
                  ·
                    refine ⟨2710994371986029953519397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1807329581324019969012931 2710994371986029953519397)
                    ·
                      refine ⟨508311444747380616284887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2710994371986029953519397 508311444747380616284887)
                      ·
                        rfl

theorem cell23_989933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_989933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989933 prefixEnd_989933 := by exact prefixLift 989933
  have htrace : WordTrace (prefixWord ++ tailWord_989933) baseStart_989933 baseEnd_989933 := by
    simpa [prefixWord, tailWord_989933, baseEnd_989933] using wordTrace_append hprefix tailTrace_989933
  have hstable : (prefixWord ++ tailWord_989933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989933).length < 2 ^ (prefixWord ++ tailWord_989933).sum := by decide
  have hdescent : baseEnd_989933 < baseStart_989933 := by decide
  rcases family_descends (prefixWord ++ tailWord_989933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989936 : List Nat := [2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 3]
def baseStart_989936 : Nat := 118140960795 + 989936 * 2 ^ 59
def prefixEnd_989936 : Nat := 4983230072969 + 3 ^ 40 * 989936 * 2
def baseEnd_989936 : Nat := 508312985189344104547373

theorem tailTrace_989936 : CollatzResearch.WordTrace tailWord_989936 prefixEnd_989936 508312985189344104547373 := by
  unfold tailWord_989936
  simp only [CollatzResearch.WordTrace]
  refine ⟨18052966070819207226874831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24070621427758942969166441 18052966070819207226874831)
  ·
    refine ⟨27079449106228810840312247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18052966070819207226874831 27079449106228810840312247)
    ·
      refine ⟨40619173659343216260468371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27079449106228810840312247 40619173659343216260468371)
      ·
        refine ⟨60928760489014824390702557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40619173659343216260468371 60928760489014824390702557)
        ·
          refine ⟨22848285183380559146513459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60928760489014824390702557 22848285183380559146513459)
          ·
            refine ⟨34272427775070838719770189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22848285183380559146513459 34272427775070838719770189)
            ·
              refine ⟨12852160415651564519913821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34272427775070838719770189 12852160415651564519913821)
              ·
                refine ⟨4819560155869336694967683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12852160415651564519913821 4819560155869336694967683)
                ·
                  refine ⟨7229340233804005042451525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4819560155869336694967683 7229340233804005042451525)
                  ·
                    refine ⟨1355501293838250945459661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7229340233804005042451525 1355501293838250945459661)
                    ·
                      refine ⟨508312985189344104547373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1355501293838250945459661 508312985189344104547373)
                      ·
                        rfl

theorem cell23_989936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 3].length) (baseStart_989936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989936 prefixEnd_989936 := by exact prefixLift 989936
  have htrace : WordTrace (prefixWord ++ tailWord_989936) baseStart_989936 baseEnd_989936 := by
    simpa [prefixWord, tailWord_989936, baseEnd_989936] using wordTrace_append hprefix tailTrace_989936
  have hstable : (prefixWord ++ tailWord_989936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989936).length < 2 ^ (prefixWord ++ tailWord_989936).sum := by decide
  have hdescent : baseEnd_989936 < baseStart_989936 := by decide
  rcases family_descends (prefixWord ++ tailWord_989936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989950 : List Nat := [4, 2, 2, 1, 2, 2, 1, 2, 2, 1, 4]
def baseStart_989950 : Nat := 118140960795 + 989950 * 2 ^ 59
def prefixEnd_989950 : Nat := 4983230072969 + 3 ^ 40 * 989950 * 2
def baseEnd_989950 : Nat := 508320173918507049772309

theorem tailTrace_989950 : CollatzResearch.WordTrace tailWord_989950 prefixEnd_989950 508320173918507049772309 := by
  unfold tailWord_989950
  simp only [CollatzResearch.WordTrace]
  refine ⟨4513305345448461855594913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24070961842391796563172869 4513305345448461855594913)
  ·
    refine ⟨3384979009086346391696185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4513305345448461855594913 3384979009086346391696185)
    ·
      refine ⟨2538734256814759793772139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3384979009086346391696185 2538734256814759793772139)
      ·
        refine ⟨3808101385222139690658209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2538734256814759793772139 3808101385222139690658209)
        ·
          refine ⟨2856076038916604767993657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3808101385222139690658209 2856076038916604767993657)
          ·
            refine ⟨2142057029187453575995243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2856076038916604767993657 2142057029187453575995243)
            ·
              refine ⟨3213085543781180363992865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2142057029187453575995243 3213085543781180363992865)
              ·
                refine ⟨2409814157835885272994649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3213085543781180363992865 2409814157835885272994649)
                ·
                  refine ⟨1807360618376913954745987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2409814157835885272994649 1807360618376913954745987)
                  ·
                    refine ⟨2711040927565370932118981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1807360618376913954745987 2711040927565370932118981)
                    ·
                      refine ⟨508320173918507049772309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2711040927565370932118981 508320173918507049772309)
                      ·
                        rfl

theorem cell23_989950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_989950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989950 prefixEnd_989950 := by exact prefixLift 989950
  have htrace : WordTrace (prefixWord ++ tailWord_989950) baseStart_989950 baseEnd_989950 := by
    simpa [prefixWord, tailWord_989950, baseEnd_989950] using wordTrace_append hprefix tailTrace_989950
  have hstable : (prefixWord ++ tailWord_989950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989950).length < 2 ^ (prefixWord ++ tailWord_989950).sum := by decide
  have hdescent : baseEnd_989950 < baseStart_989950 := by decide
  rcases family_descends (prefixWord ++ tailWord_989950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989956 : List Nat := [2, 3, 2, 2, 1, 1, 1, 3, 8]
def baseStart_989956 : Nat := 118140960795 + 989956 * 2 ^ 59
def prefixEnd_989956 : Nat := 4983230072969 + 3 ^ 40 * 989956 * 2
def baseEnd_989956 : Nat := 56480361644714891810809

theorem tailTrace_989956 : CollatzResearch.WordTrace tailWord_989956 prefixEnd_989956 56480361644714891810809 := by
  unfold tailWord_989956
  simp only [CollatzResearch.WordTrace]
  refine ⟨18053330800782978934738861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24071107734377305246318481 18053330800782978934738861)
  ·
    refine ⟨6769999050293617100527073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18053330800782978934738861 6769999050293617100527073)
    ·
      refine ⟨5077499287720212825395305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6769999050293617100527073 5077499287720212825395305)
      ·
        refine ⟨3808124465790159619046479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5077499287720212825395305 3808124465790159619046479)
        ·
          refine ⟨5712186698685239428569719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3808124465790159619046479 5712186698685239428569719)
          ·
            refine ⟨8568280048027859142854579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5712186698685239428569719 8568280048027859142854579)
            ·
              refine ⟨12852420072041788714281869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8568280048027859142854579 12852420072041788714281869)
              ·
                refine ⟨4819657527015670767855701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12852420072041788714281869 4819657527015670767855701)
                ·
                  refine ⟨56480361644714891810809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4819657527015670767855701 56480361644714891810809)
                  ·
                    rfl

theorem cell23_989956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 8].length) (baseStart_989956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989956 prefixEnd_989956 := by exact prefixLift 989956
  have htrace : WordTrace (prefixWord ++ tailWord_989956) baseStart_989956 baseEnd_989956 := by
    simpa [prefixWord, tailWord_989956, baseEnd_989956] using wordTrace_append hprefix tailTrace_989956
  have hstable : (prefixWord ++ tailWord_989956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989956).length < 2 ^ (prefixWord ++ tailWord_989956).sum := by decide
  have hdescent : baseEnd_989956 < baseStart_989956 := by decide
  rcases family_descends (prefixWord ++ tailWord_989956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989960 : List Nat := [2, 1, 3, 2, 2, 4, 1, 1, 3, 4]
def baseStart_989960 : Nat := 118140960795 + 989960 * 2 ^ 59
def prefixEnd_989960 : Nat := 4983230072969 + 3 ^ 40 * 989960 * 2
def baseEnd_989960 : Nat := 169441769575017336882421

theorem tailTrace_989960 : CollatzResearch.WordTrace tailWord_989960 prefixEnd_989960 169441769575017336882421 := by
  unfold tailWord_989960
  simp only [CollatzResearch.WordTrace]
  refine ⟨18053403746775733276311667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24071204995700977701748889 18053403746775733276311667)
  ·
    refine ⟨27080105620163599914467501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18053403746775733276311667 27080105620163599914467501)
    ·
      refine ⟨10155039607561349967925313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27080105620163599914467501 10155039607561349967925313)
      ·
        refine ⟨7616279705671012475943985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10155039607561349967925313 7616279705671012475943985)
        ·
          refine ⟨5712209779253259356957989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7616279705671012475943985 5712209779253259356957989)
          ·
            refine ⟨1071039333609986129429623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5712209779253259356957989 1071039333609986129429623)
            ·
              refine ⟨1606559000414979194144435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1071039333609986129429623 1606559000414979194144435)
              ·
                refine ⟨2409838500622468791216653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1606559000414979194144435 2409838500622468791216653)
                ·
                  refine ⟨903689437733425796706245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2409838500622468791216653 903689437733425796706245)
                  ·
                    refine ⟨169441769575017336882421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 903689437733425796706245 169441769575017336882421)
                    ·
                      rfl

theorem cell23_989960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 3, 4].length) (baseStart_989960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989960 prefixEnd_989960 := by exact prefixLift 989960
  have htrace : WordTrace (prefixWord ++ tailWord_989960) baseStart_989960 baseEnd_989960 := by
    simpa [prefixWord, tailWord_989960, baseEnd_989960] using wordTrace_append hprefix tailTrace_989960
  have hstable : (prefixWord ++ tailWord_989960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989960).length < 2 ^ (prefixWord ++ tailWord_989960).sum := by decide
  have hdescent : baseEnd_989960 < baseStart_989960 := by decide
  rcases family_descends (prefixWord ++ tailWord_989960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989993 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 6, 3, 2]
def baseStart_989993 : Nat := 118140960795 + 989993 * 2 ^ 59
def prefixEnd_989993 : Nat := 4983230072969 + 3 ^ 40 * 989993 * 2
def baseEnd_989993 : Nat := 508342253586650381534611

theorem tailTrace_989993 : CollatzResearch.WordTrace tailWord_989993 prefixEnd_989993 508342253586650381534611 := by
  unfold tailWord_989993
  simp only [CollatzResearch.WordTrace]
  refine ⟨36108011102431913188574633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24072007401621275459049755 36108011102431913188574633)
  ·
    refine ⟨27081008326823934891430975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36108011102431913188574633 27081008326823934891430975)
    ·
      refine ⟨40621512490235902337146463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27081008326823934891430975 40621512490235902337146463)
      ·
        refine ⟨60932268735353853505719695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40621512490235902337146463 60932268735353853505719695)
        ·
          refine ⟨91398403103030780258579543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60932268735353853505719695 91398403103030780258579543)
          ·
            refine ⟨137097604654546170387869315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91398403103030780258579543 137097604654546170387869315)
            ·
              refine ⟨205646406981819255581803973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137097604654546170387869315 205646406981819255581803973)
              ·
                refine ⟨38558701309091110421588245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 205646406981819255581803973 38558701309091110421588245)
                ·
                  refine ⟨1807439123863645801011949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 38558701309091110421588245 1807439123863645801011949)
                  ·
                    refine ⟨677789671448867175379481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1807439123863645801011949 677789671448867175379481)
                    ·
                      refine ⟨508342253586650381534611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 677789671448867175379481 508342253586650381534611)
                      ·
                        rfl

theorem cell23_989993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 6, 3, 2].length) (baseStart_989993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_989993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_989993 prefixEnd_989993 := by exact prefixLift 989993
  have htrace : WordTrace (prefixWord ++ tailWord_989993) baseStart_989993 baseEnd_989993 := by
    simpa [prefixWord, tailWord_989993, baseEnd_989993] using wordTrace_append hprefix tailTrace_989993
  have hstable : (prefixWord ++ tailWord_989993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989993).length < 2 ^ (prefixWord ++ tailWord_989993).sum := by decide
  have hdescent : baseEnd_989993 < baseStart_989993 := by decide
  rcases family_descends (prefixWord ++ tailWord_989993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990023 : List Nat := [1, 1, 4, 1, 2, 1, 1, 2, 2, 6, 2]
def baseStart_990023 : Nat := 118140960795 + 990023 * 2 ^ 59
def prefixEnd_990023 : Nat := 4983230072969 + 3 ^ 40 * 990023 * 2
def baseEnd_990023 : Nat := 508357658006285264159473

theorem tailTrace_990023 : CollatzResearch.WordTrace tailWord_990023 prefixEnd_990023 508357658006285264159473 := by
  unfold tailWord_990023
  simp only [CollatzResearch.WordTrace]
  refine ⟨36109105292323228312166723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24072736861548818874777815 36109105292323228312166723)
  ·
    refine ⟨54163657938484842468250085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36109105292323228312166723 54163657938484842468250085)
    ·
      refine ⟨10155685863465907962796891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54163657938484842468250085 10155685863465907962796891)
      ·
        refine ⟨15233528795198861944195337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10155685863465907962796891 15233528795198861944195337)
        ·
          refine ⟨11425146596399146458146503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15233528795198861944195337 11425146596399146458146503)
          ·
            refine ⟨17137719894598719687219755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11425146596399146458146503 17137719894598719687219755)
            ·
              refine ⟨25706579841898079530829633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17137719894598719687219755 25706579841898079530829633)
              ·
                refine ⟨19279934881423559648122225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25706579841898079530829633 19279934881423559648122225)
                ·
                  refine ⟨14459951161067669736091669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19279934881423559648122225 14459951161067669736091669)
                  ·
                    refine ⟨677810210675047018879297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14459951161067669736091669 677810210675047018879297)
                    ·
                      refine ⟨508357658006285264159473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 677810210675047018879297 508357658006285264159473)
                      ·
                        rfl

theorem cell23_990023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 6, 2].length) (baseStart_990023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990023 prefixEnd_990023 := by exact prefixLift 990023
  have htrace : WordTrace (prefixWord ++ tailWord_990023) baseStart_990023 baseEnd_990023 := by
    simpa [prefixWord, tailWord_990023, baseEnd_990023] using wordTrace_append hprefix tailTrace_990023
  have hstable : (prefixWord ++ tailWord_990023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990023).length < 2 ^ (prefixWord ++ tailWord_990023).sum := by decide
  have hdescent : baseEnd_990023 < baseStart_990023 := by decide
  rcases family_descends (prefixWord ++ tailWord_990023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990044 : List Nat := [2, 2, 4, 2, 1, 3, 1, 1, 2, 3, 2]
def baseStart_990044 : Nat := 118140960795 + 990044 * 2 ^ 59
def prefixEnd_990044 : Nat := 4983230072969 + 3 ^ 40 * 990044 * 2
def baseEnd_990044 : Nat := 508368441100029681996877

theorem tailTrace_990044 : CollatzResearch.WordTrace tailWord_990044 prefixEnd_990044 508368441100029681996877 := by
  unfold tailWord_990044
  simp only [CollatzResearch.WordTrace]
  refine ⟨18054935612623574449340593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24073247483498099265787457 18054935612623574449340593)
  ·
    refine ⟨13541201709467680837005445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18054935612623574449340593 13541201709467680837005445)
    ·
      refine ⟨2538975320525190156938521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13541201709467680837005445 2538975320525190156938521)
      ·
        refine ⟨1904231490393892617703891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2538975320525190156938521 1904231490393892617703891)
        ·
          refine ⟨2856347235590838926555837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1904231490393892617703891 2856347235590838926555837)
          ·
            refine ⟨1071130213346564597458439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2856347235590838926555837 1071130213346564597458439)
            ·
              refine ⟨1606695320019846896187659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1071130213346564597458439 1606695320019846896187659)
              ·
                refine ⟨2410042980029770344281489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1606695320019846896187659 2410042980029770344281489)
                ·
                  refine ⟨1807532235022327758211117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2410042980029770344281489 1807532235022327758211117)
                  ·
                    refine ⟨677824588133372909329169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1807532235022327758211117 677824588133372909329169)
                    ·
                      refine ⟨508368441100029681996877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 677824588133372909329169 508368441100029681996877)
                      ·
                        rfl

theorem cell23_990044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_990044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990044 prefixEnd_990044 := by exact prefixLift 990044
  have htrace : WordTrace (prefixWord ++ tailWord_990044) baseStart_990044 baseEnd_990044 := by
    simpa [prefixWord, tailWord_990044, baseEnd_990044] using wordTrace_append hprefix tailTrace_990044
  have hstable : (prefixWord ++ tailWord_990044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990044).length < 2 ^ (prefixWord ++ tailWord_990044).sum := by decide
  have hdescent : baseEnd_990044 < baseStart_990044 := by decide
  rcases family_descends (prefixWord ++ tailWord_990044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990053 : List Nat := [1, 3, 1, 3, 1, 1, 4, 2, 1, 2, 4]
def baseStart_990053 : Nat := 118140960795 + 990053 * 2 ^ 59
def prefixEnd_990053 : Nat := 4983230072969 + 3 ^ 40 * 990053 * 2
def baseEnd_990053 : Nat := 508373062425920146784335

theorem tailTrace_990053 : CollatzResearch.WordTrace tailWord_990053 prefixEnd_990053 508373062425920146784335 := by
  unfold tailWord_990053
  simp only [CollatzResearch.WordTrace]
  refine ⟨36110199482214543435758813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24073466321476362290505875 36110199482214543435758813)
  ·
    refine ⟨13541324805830453788409555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36110199482214543435758813 13541324805830453788409555)
    ·
      refine ⟨20311987208745680682614333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13541324805830453788409555 20311987208745680682614333)
      ·
        refine ⟨7616995203279630255980375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20311987208745680682614333 7616995203279630255980375)
        ·
          refine ⟨11425492804919445383970563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7616995203279630255980375 11425492804919445383970563)
          ·
            refine ⟨17138239207379168075955845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11425492804919445383970563 17138239207379168075955845)
            ·
              refine ⟨3213419851383594014241721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17138239207379168075955845 3213419851383594014241721)
              ·
                refine ⟨2410064888537695510681291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3213419851383594014241721 2410064888537695510681291)
                ·
                  refine ⟨3615097332806543266021937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2410064888537695510681291 3615097332806543266021937)
                  ·
                    refine ⟨2711322999604907449516453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3615097332806543266021937 2711322999604907449516453)
                    ·
                      refine ⟨508373062425920146784335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2711322999604907449516453 508373062425920146784335)
                      ·
                        rfl

theorem cell23_990053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_990053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990053 prefixEnd_990053 := by exact prefixLift 990053
  have htrace : WordTrace (prefixWord ++ tailWord_990053) baseStart_990053 baseEnd_990053 := by
    simpa [prefixWord, tailWord_990053, baseEnd_990053] using wordTrace_append hprefix tailTrace_990053
  have hstable : (prefixWord ++ tailWord_990053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990053).length < 2 ^ (prefixWord ++ tailWord_990053).sum := by decide
  have hdescent : baseEnd_990053 < baseStart_990053 := by decide
  rcases family_descends (prefixWord ++ tailWord_990053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990060 : List Nat := [2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 3]
def baseStart_990060 : Nat := 118140960795 + 990060 * 2 ^ 59
def prefixEnd_990060 : Nat := 4983230072969 + 3 ^ 40 * 990060 * 2
def baseEnd_990060 : Nat := 508376656790501619396803

theorem tailTrace_990060 : CollatzResearch.WordTrace tailWord_990060 prefixEnd_990060 508376656790501619396803 := by
  unfold tailWord_990060
  simp only [CollatzResearch.WordTrace]
  refine ⟨18055227396594591815631817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24073636528792789087509089 18055227396594591815631817)
  ·
    refine ⟨13541420547445943861723863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18055227396594591815631817 13541420547445943861723863)
    ·
      refine ⟨20312130821168915792585795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13541420547445943861723863 20312130821168915792585795)
      ·
        refine ⟨30468196231753373688878693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20312130821168915792585795 30468196231753373688878693)
        ·
          refine ⟨5712786793453757566664755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30468196231753373688878693 5712786793453757566664755)
          ·
            refine ⟨8569180190180636349997133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5712786793453757566664755 8569180190180636349997133)
            ·
              refine ⟨3213442571317738631248925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8569180190180636349997133 3213442571317738631248925)
              ·
                refine ⟨1205040964244151986718347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3213442571317738631248925 1205040964244151986718347)
                ·
                  refine ⟨1807561446366227980077521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1205040964244151986718347 1807561446366227980077521)
                  ·
                    refine ⟨1355671084774670985058141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1807561446366227980077521 1355671084774670985058141)
                    ·
                      refine ⟨508376656790501619396803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1355671084774670985058141 508376656790501619396803)
                      ·
                        rfl

theorem cell23_990060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 3].length) (baseStart_990060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990060 prefixEnd_990060 := by exact prefixLift 990060
  have htrace : WordTrace (prefixWord ++ tailWord_990060) baseStart_990060 baseEnd_990060 := by
    simpa [prefixWord, tailWord_990060, baseEnd_990060] using wordTrace_append hprefix tailTrace_990060
  have hstable : (prefixWord ++ tailWord_990060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990060).length < 2 ^ (prefixWord ++ tailWord_990060).sum := by decide
  have hdescent : baseEnd_990060 < baseStart_990060 := by decide
  rcases family_descends (prefixWord ++ tailWord_990060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990076 : List Nat := [2, 2, 2, 1, 1, 1, 1, 3, 1, 9]
def baseStart_990076 : Nat := 118140960795 + 990076 * 2 ^ 59
def prefixEnd_990076 : Nat := 4983230072969 + 3 ^ 40 * 990076 * 2
def baseEnd_990076 : Nat := 169461624160324518932243

theorem tailTrace_990076 : CollatzResearch.WordTrace tailWord_990076 prefixEnd_990076 169461624160324518932243 := by
  unfold tailWord_990076
  simp only [CollatzResearch.WordTrace]
  refine ⟨18055519180565609181923041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24074025574087478909230721 18055519180565609181923041)
  ·
    refine ⟨13541639385424206886442281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18055519180565609181923041 13541639385424206886442281)
    ·
      refine ⟨10156229539068155164831711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13541639385424206886442281 10156229539068155164831711)
      ·
        refine ⟨15234344308602232747247567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10156229539068155164831711 15234344308602232747247567)
        ·
          refine ⟨22851516462903349120871351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15234344308602232747247567 22851516462903349120871351)
          ·
            refine ⟨34277274694355023681307027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22851516462903349120871351 34277274694355023681307027)
            ·
              refine ⟨51415912041532535521960541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34277274694355023681307027 51415912041532535521960541)
              ·
                refine ⟨19280967015574700820735203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51415912041532535521960541 19280967015574700820735203)
                ·
                  refine ⟨28921450523362051231102805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19280967015574700820735203 28921450523362051231102805)
                  ·
                    refine ⟨169461624160324518932243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 28921450523362051231102805 169461624160324518932243)
                    ·
                      rfl

theorem cell23_990076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 1, 9].length) (baseStart_990076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990076 prefixEnd_990076 := by exact prefixLift 990076
  have htrace : WordTrace (prefixWord ++ tailWord_990076) baseStart_990076 baseEnd_990076 := by
    simpa [prefixWord, tailWord_990076, baseEnd_990076] using wordTrace_append hprefix tailTrace_990076
  have hstable : (prefixWord ++ tailWord_990076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990076).length < 2 ^ (prefixWord ++ tailWord_990076).sum := by decide
  have hdescent : baseEnd_990076 < baseStart_990076 := by decide
  rcases family_descends (prefixWord ++ tailWord_990076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990108 : List Nat := [2, 2, 3, 3, 2, 2, 1, 3, 1, 2, 2]
def baseStart_990108 : Nat := 118140960795 + 990108 * 2 ^ 59
def prefixEnd_990108 : Nat := 4983230072969 + 3 ^ 40 * 990108 * 2
def baseEnd_990108 : Nat := 508401303861917431596583

theorem tailTrace_990108 : CollatzResearch.WordTrace tailWord_990108 prefixEnd_990108 508401303861917431596583 := by
  unfold tailWord_990108
  simp only [CollatzResearch.WordTrace]
  refine ⟨18056102748507643914505489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24074803664676858552673985 18056102748507643914505489)
  ·
    refine ⟨13542077061380732935879117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18056102748507643914505489 13542077061380732935879117)
    ·
      refine ⟨5078278898017774850954669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13542077061380732935879117 5078278898017774850954669)
      ·
        refine ⟨1904354586756665569108001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5078278898017774850954669 1904354586756665569108001)
        ·
          refine ⟨1428265940067499176831001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1904354586756665569108001 1428265940067499176831001)
          ·
            refine ⟨1071199455050624382623251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1428265940067499176831001 1071199455050624382623251)
            ·
              refine ⟨1606799182575936573934877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1071199455050624382623251 1606799182575936573934877)
              ·
                refine ⟨602549693465976215225579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1606799182575936573934877 602549693465976215225579)
                ·
                  refine ⟨903824540198964322838369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 602549693465976215225579 903824540198964322838369)
                  ·
                    refine ⟨677868405149223242128777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 903824540198964322838369 677868405149223242128777)
                    ·
                      refine ⟨508401303861917431596583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 677868405149223242128777 508401303861917431596583)
                      ·
                        rfl

theorem cell23_990108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_990108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990108 prefixEnd_990108 := by exact prefixLift 990108
  have htrace : WordTrace (prefixWord ++ tailWord_990108) baseStart_990108 baseEnd_990108 := by
    simpa [prefixWord, tailWord_990108, baseEnd_990108] using wordTrace_append hprefix tailTrace_990108
  have hstable : (prefixWord ++ tailWord_990108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990108).length < 2 ^ (prefixWord ++ tailWord_990108).sum := by decide
  have hdescent : baseEnd_990108 < baseStart_990108 := by decide
  rcases family_descends (prefixWord ++ tailWord_990108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990125 : List Nat := [1, 5, 2, 3, 1, 1, 3, 2, 1, 2, 2]
def baseStart_990125 : Nat := 118140960795 + 990125 * 2 ^ 59
def prefixEnd_990125 : Nat := 4983230072969 + 3 ^ 40 * 990125 * 2
def baseEnd_990125 : Nat := 508410033033043865084005

theorem tailTrace_990125 : CollatzResearch.WordTrace tailWord_990125 prefixEnd_990125 508410033033043865084005 := by
  unfold tailWord_990125
  simp only [CollatzResearch.WordTrace]
  refine ⟨36112825537953699732379829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24075217025302466488253219 36112825537953699732379829)
  ·
    refine ⟨3385577394183159349910609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36112825537953699732379829 3385577394183159349910609)
    ·
      refine ⟨2539183045637369512432957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3385577394183159349910609 2539183045637369512432957)
      ·
        refine ⟨952193642114013567162359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2539183045637369512432957 952193642114013567162359)
        ·
          refine ⟨1428290463171020350743539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 952193642114013567162359 1428290463171020350743539)
          ·
            refine ⟨2142435694756530526115309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1428290463171020350743539 2142435694756530526115309)
            ·
              refine ⟨803413385533698947293241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2142435694756530526115309 803413385533698947293241)
              ·
                refine ⟨602560039150274210469931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 803413385533698947293241 602560039150274210469931)
                ·
                  refine ⟨903840058725411315704897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 602560039150274210469931 903840058725411315704897)
                  ·
                    refine ⟨677880044044058486778673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 903840058725411315704897 677880044044058486778673)
                    ·
                      refine ⟨508410033033043865084005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 677880044044058486778673 508410033033043865084005)
                      ·
                        rfl

theorem cell23_990125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_990125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990125 prefixEnd_990125 := by exact prefixLift 990125
  have htrace : WordTrace (prefixWord ++ tailWord_990125) baseStart_990125 baseEnd_990125 := by
    simpa [prefixWord, tailWord_990125, baseEnd_990125] using wordTrace_append hprefix tailTrace_990125
  have hstable : (prefixWord ++ tailWord_990125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990125).length < 2 ^ (prefixWord ++ tailWord_990125).sum := by decide
  have hdescent : baseEnd_990125 < baseStart_990125 := by decide
  rcases family_descends (prefixWord ++ tailWord_990125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990133 : List Nat := [1, 3, 3, 2, 1, 1, 1, 2, 1, 3, 5]
def baseStart_990133 : Nat := 118140960795 + 990133 * 2 ^ 59
def prefixEnd_990133 : Nat := 4983230072969 + 3 ^ 40 * 990133 * 2
def baseEnd_990133 : Nat := 508414140878279833783967

theorem tailTrace_990133 : CollatzResearch.WordTrace tailWord_990133 prefixEnd_990133 508414140878279833783967 := by
  unfold tailWord_990133
  simp only [CollatzResearch.WordTrace]
  refine ⟨36113117321924717098671053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24075411547949811399114035 36113117321924717098671053)
  ·
    refine ⟨13542418995721768912001645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36113117321924717098671053 13542418995721768912001645)
    ·
      refine ⟨5078407123395663342000617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13542418995721768912001645 5078407123395663342000617)
      ·
        refine ⟨3808805342546747506500463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5078407123395663342000617 3808805342546747506500463)
        ·
          refine ⟨5713208013820121259750695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3808805342546747506500463 5713208013820121259750695)
          ·
            refine ⟨8569812020730181889626043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5713208013820121259750695 8569812020730181889626043)
            ·
              refine ⟨12854718031095272834439065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8569812020730181889626043 12854718031095272834439065)
              ·
                refine ⟨9641038523321454625829299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12854718031095272834439065 9641038523321454625829299)
                ·
                  refine ⟨14461557784982181938743949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9641038523321454625829299 14461557784982181938743949)
                  ·
                    refine ⟨5423084169368318227028981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14461557784982181938743949 5423084169368318227028981)
                    ·
                      refine ⟨508414140878279833783967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5423084169368318227028981 508414140878279833783967)
                      ·
                        rfl

theorem cell23_990133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_990133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990133 prefixEnd_990133 := by exact prefixLift 990133
  have htrace : WordTrace (prefixWord ++ tailWord_990133) baseStart_990133 baseEnd_990133 := by
    simpa [prefixWord, tailWord_990133, baseEnd_990133] using wordTrace_append hprefix tailTrace_990133
  have hstable : (prefixWord ++ tailWord_990133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990133).length < 2 ^ (prefixWord ++ tailWord_990133).sum := by decide
  have hdescent : baseEnd_990133 < baseStart_990133 := by decide
  rcases family_descends (prefixWord ++ tailWord_990133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990141 : List Nat := [1, 4, 1, 2, 4, 2, 2, 1, 2, 1, 3]
def baseStart_990141 : Nat := 118140960795 + 990141 * 2 ^ 59
def prefixEnd_990141 : Nat := 4983230072969 + 3 ^ 40 * 990141 * 2
def baseEnd_990141 : Nat := 508418248723515802483931

theorem tailTrace_990141 : CollatzResearch.WordTrace tailWord_990141 prefixEnd_990141 508418248723515802483931 := by
  unfold tailWord_990141
  simp only [CollatzResearch.WordTrace]
  refine ⟨36113409105895734464962277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24075606070597156309974851 36113409105895734464962277)
  ·
    refine ⟨6771264207355450212180427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36113409105895734464962277 6771264207355450212180427)
    ·
      refine ⟨10156896311033175318270641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6771264207355450212180427 10156896311033175318270641)
      ·
        refine ⟨7617672233274881488702981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10156896311033175318270641 7617672233274881488702981)
        ·
          refine ⟨1428313543739040279131809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7617672233274881488702981 1428313543739040279131809)
          ·
            refine ⟨1071235157804280209348857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1428313543739040279131809 1071235157804280209348857)
            ·
              refine ⟨803426368353210157011643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1071235157804280209348857 803426368353210157011643)
              ·
                refine ⟨1205139552529815235517465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 803426368353210157011643 1205139552529815235517465)
                ·
                  refine ⟨903854664397361426638099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1205139552529815235517465 903854664397361426638099)
                  ·
                    refine ⟨1355781996596042139957149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 903854664397361426638099 1355781996596042139957149)
                    ·
                      refine ⟨508418248723515802483931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1355781996596042139957149 508418248723515802483931)
                      ·
                        rfl

theorem cell23_990141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 1, 2, 1, 3].length) (baseStart_990141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990141 prefixEnd_990141 := by exact prefixLift 990141
  have htrace : WordTrace (prefixWord ++ tailWord_990141) baseStart_990141 baseEnd_990141 := by
    simpa [prefixWord, tailWord_990141, baseEnd_990141] using wordTrace_append hprefix tailTrace_990141
  have hstable : (prefixWord ++ tailWord_990141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990141).length < 2 ^ (prefixWord ++ tailWord_990141).sum := by decide
  have hdescent : baseEnd_990141 < baseStart_990141 := by decide
  rcases family_descends (prefixWord ++ tailWord_990141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990147 : List Nat := [1, 1, 1, 3, 1, 1, 2, 7, 2, 2, 2]
def baseStart_990147 : Nat := 118140960795 + 990147 * 2 ^ 59
def prefixEnd_990147 : Nat := 4983230072969 + 3 ^ 40 * 990147 * 2
def baseEnd_990147 : Nat := 508421329607442779008903

theorem tailTrace_990147 : CollatzResearch.WordTrace tailWord_990147 prefixEnd_990147 508421329607442779008903 := by
  unfold tailWord_990147
  simp only [CollatzResearch.WordTrace]
  refine ⟨36113627943873997489680695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24075751962582664993120463 36113627943873997489680695)
  ·
    refine ⟨54170441915810996234521043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36113627943873997489680695 54170441915810996234521043)
    ·
      refine ⟨81255662873716494351781565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54170441915810996234521043 81255662873716494351781565)
      ·
        refine ⟨30470873577643685381918087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81255662873716494351781565 30470873577643685381918087)
        ·
          refine ⟨45706310366465528072877131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30470873577643685381918087 45706310366465528072877131)
          ·
            refine ⟨68559465549698292109315697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45706310366465528072877131 68559465549698292109315697)
            ·
              refine ⟨51419599162273719081986773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68559465549698292109315697 51419599162273719081986773)
              ·
                refine ⟨1205146855365790290984065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 51419599162273719081986773 1205146855365790290984065)
                ·
                  refine ⟨903860141524342718238049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1205146855365790290984065 903860141524342718238049)
                  ·
                    refine ⟨677895106143257038678537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 903860141524342718238049 677895106143257038678537)
                    ·
                      refine ⟨508421329607442779008903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 677895106143257038678537 508421329607442779008903)
                      ·
                        rfl

theorem cell23_990147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 7, 2, 2, 2].length) (baseStart_990147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990147 prefixEnd_990147 := by exact prefixLift 990147
  have htrace : WordTrace (prefixWord ++ tailWord_990147) baseStart_990147 baseEnd_990147 := by
    simpa [prefixWord, tailWord_990147, baseEnd_990147] using wordTrace_append hprefix tailTrace_990147
  have hstable : (prefixWord ++ tailWord_990147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990147).length < 2 ^ (prefixWord ++ tailWord_990147).sum := by decide
  have hdescent : baseEnd_990147 < baseStart_990147 := by decide
  rcases family_descends (prefixWord ++ tailWord_990147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990203 : List Nat := [1, 1, 1, 1, 1, 3, 3, 4, 1, 3, 4]
def baseStart_990203 : Nat := 118140960795 + 990203 * 2 ^ 59
def prefixEnd_990203 : Nat := 4983230072969 + 3 ^ 40 * 990203 * 2
def baseEnd_990203 : Nat := 508450084524094559908645

theorem tailTrace_990203 : CollatzResearch.WordTrace tailWord_990203 prefixEnd_990203 508450084524094559908645 := by
  unfold tailWord_990203
  simp only [CollatzResearch.WordTrace]
  refine ⟨36115670431671119053719263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24077113621114079369146175 36115670431671119053719263)
  ·
    refine ⟨54173505647506678580578895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36115670431671119053719263 54173505647506678580578895)
    ·
      refine ⟨81260258471260017870868343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54173505647506678580578895 81260258471260017870868343)
      ·
        refine ⟨121890387706890026806302515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81260258471260017870868343 121890387706890026806302515)
        ·
          refine ⟨182835581560335040209453773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121890387706890026806302515 182835581560335040209453773)
          ·
            refine ⟨68563343085125640078545165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182835581560335040209453773 68563343085125640078545165)
            ·
              refine ⟨25711253656922115029454437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68563343085125640078545165 25711253656922115029454437)
              ·
                refine ⟨4820860060672896568022707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25711253656922115029454437 4820860060672896568022707)
                ·
                  refine ⟨7231290091009344852034061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4820860060672896568022707 7231290091009344852034061)
                  ·
                    refine ⟨2711733784128504319512773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7231290091009344852034061 2711733784128504319512773)
                    ·
                      refine ⟨508450084524094559908645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2711733784128504319512773 508450084524094559908645)
                      ·
                        rfl

theorem cell23_990203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 3, 4].length) (baseStart_990203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990203 prefixEnd_990203 := by exact prefixLift 990203
  have htrace : WordTrace (prefixWord ++ tailWord_990203) baseStart_990203 baseEnd_990203 := by
    simpa [prefixWord, tailWord_990203, baseEnd_990203] using wordTrace_append hprefix tailTrace_990203
  have hstable : (prefixWord ++ tailWord_990203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990203).length < 2 ^ (prefixWord ++ tailWord_990203).sum := by decide
  have hdescent : baseEnd_990203 < baseStart_990203 := by decide
  rcases family_descends (prefixWord ++ tailWord_990203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990220 : List Nat := [2, 2, 1, 2, 3, 3, 1, 1, 1, 3, 4]
def baseStart_990220 : Nat := 118140960795 + 990220 * 2 ^ 59
def prefixEnd_990220 : Nat := 4983230072969 + 3 ^ 40 * 990220 * 2
def baseEnd_990220 : Nat := 508458813695220993396067

theorem tailTrace_990220 : CollatzResearch.WordTrace tailWord_990220 prefixEnd_990220 508458813695220993396067 := by
  unfold tailWord_990220
  simp only [CollatzResearch.WordTrace]
  refine ⟨18058145236304765478544057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24077526981739687304725409 18058145236304765478544057)
  ·
    refine ⟨13543608927228574108908043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18058145236304765478544057 13543608927228574108908043)
    ·
      refine ⟨20315413390842861163362065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13543608927228574108908043 20315413390842861163362065)
      ·
        refine ⟨15236560043132145872521549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20315413390842861163362065 15236560043132145872521549)
        ·
          refine ⟨5713710016174554702195581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15236560043132145872521549 5713710016174554702195581)
          ·
            refine ⟨2142641256065458013323343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5713710016174554702195581 2142641256065458013323343)
            ·
              refine ⟨3213961884098187019985015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2142641256065458013323343 3213961884098187019985015)
              ·
                refine ⟨4820942826147280529977523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3213961884098187019985015 4820942826147280529977523)
                ·
                  refine ⟨7231414239220920794966285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4820942826147280529977523 7231414239220920794966285)
                  ·
                    refine ⟨2711780339707845298112357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7231414239220920794966285 2711780339707845298112357)
                    ·
                      refine ⟨508458813695220993396067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2711780339707845298112357 508458813695220993396067)
                      ·
                        rfl

theorem cell23_990220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_990220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990220 prefixEnd_990220 := by exact prefixLift 990220
  have htrace : WordTrace (prefixWord ++ tailWord_990220) baseStart_990220 baseEnd_990220 := by
    simpa [prefixWord, tailWord_990220, baseEnd_990220] using wordTrace_append hprefix tailTrace_990220
  have hstable : (prefixWord ++ tailWord_990220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990220).length < 2 ^ (prefixWord ++ tailWord_990220).sum := by decide
  have hdescent : baseEnd_990220 < baseStart_990220 := by decide
  rcases family_descends (prefixWord ++ tailWord_990220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990233 : List Nat := [1, 2, 1, 2, 1, 1, 5, 1, 2, 1, 6]
def baseStart_990233 : Nat := 118140960795 + 990233 * 2 ^ 59
def prefixEnd_990233 : Nat := 4983230072969 + 3 ^ 40 * 990233 * 2
def baseEnd_990233 : Nat := 508465488943729442533507

theorem tailTrace_990233 : CollatzResearch.WordTrace tailWord_990233 prefixEnd_990233 508465488943729442533507 := by
  unfold tailWord_990233
  simp only [CollatzResearch.WordTrace]
  refine ⟨36116764621562434177311353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24077843081041622784874235 36116764621562434177311353)
  ·
    refine ⟨27087573466171825632983515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36116764621562434177311353 27087573466171825632983515)
    ·
      refine ⟨40631360199257738449475273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27087573466171825632983515 40631360199257738449475273)
      ·
        refine ⟨30473520149443303837106455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40631360199257738449475273 30473520149443303837106455)
        ·
          refine ⟨45710280224164955755659683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30473520149443303837106455 45710280224164955755659683)
          ·
            refine ⟨68565420336247433633489525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45710280224164955755659683 68565420336247433633489525)
            ·
              refine ⟨6428008156523196903139643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68565420336247433633489525 6428008156523196903139643)
              ·
                refine ⟨9642012234784795354709465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6428008156523196903139643 9642012234784795354709465)
                ·
                  refine ⟨7231509176088596516032099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9642012234784795354709465 7231509176088596516032099)
                  ·
                    refine ⟨10847263764132894774048149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7231509176088596516032099 10847263764132894774048149)
                    ·
                      refine ⟨508465488943729442533507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10847263764132894774048149 508465488943729442533507)
                      ·
                        rfl

theorem cell23_990233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 1, 6].length) (baseStart_990233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990233 prefixEnd_990233 := by exact prefixLift 990233
  have htrace : WordTrace (prefixWord ++ tailWord_990233) baseStart_990233 baseEnd_990233 := by
    simpa [prefixWord, tailWord_990233, baseEnd_990233] using wordTrace_append hprefix tailTrace_990233
  have hstable : (prefixWord ++ tailWord_990233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990233).length < 2 ^ (prefixWord ++ tailWord_990233).sum := by decide
  have hdescent : baseEnd_990233 < baseStart_990233 := by decide
  rcases family_descends (prefixWord ++ tailWord_990233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990263 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 6]
def baseStart_990263 : Nat := 118140960795 + 990263 * 2 ^ 59
def prefixEnd_990263 : Nat := 4983230072969 + 3 ^ 40 * 990263 * 2
def baseEnd_990263 : Nat := 508480893363364325158369

theorem tailTrace_990263 : CollatzResearch.WordTrace tailWord_990263 prefixEnd_990263 508480893363364325158369 := by
  unfold tailWord_990263
  simp only [CollatzResearch.WordTrace]
  refine ⟨36117858811453749300903443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24078572540969166200602295 36117858811453749300903443)
  ·
    refine ⟨54176788217180623951355165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36117858811453749300903443 54176788217180623951355165)
    ·
      refine ⟨20316295581442733981758187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54176788217180623951355165 20316295581442733981758187)
      ·
        refine ⟨30474443372164100972637281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20316295581442733981758187 30474443372164100972637281)
        ·
          refine ⟨22855832529123075729477961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30474443372164100972637281 22855832529123075729477961)
          ·
            refine ⟨17141874396842306797108471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22855832529123075729477961 17141874396842306797108471)
            ·
              refine ⟨25712811595263460195662707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17141874396842306797108471 25712811595263460195662707)
              ·
                refine ⟨38569217392895190293494061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25712811595263460195662707 38569217392895190293494061)
                ·
                  refine ⟨14463456522335696360060273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38569217392895190293494061 14463456522335696360060273)
                  ·
                    refine ⟨10847592391751772270045205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14463456522335696360060273 10847592391751772270045205)
                    ·
                      refine ⟨508480893363364325158369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10847592391751772270045205 508480893363364325158369)
                      ·
                        rfl

theorem cell23_990263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 6].length) (baseStart_990263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990263 prefixEnd_990263 := by exact prefixLift 990263
  have htrace : WordTrace (prefixWord ++ tailWord_990263) baseStart_990263 baseEnd_990263 := by
    simpa [prefixWord, tailWord_990263, baseEnd_990263] using wordTrace_append hprefix tailTrace_990263
  have hstable : (prefixWord ++ tailWord_990263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990263).length < 2 ^ (prefixWord ++ tailWord_990263).sum := by decide
  have hdescent : baseEnd_990263 < baseStart_990263 := by decide
  rcases family_descends (prefixWord ++ tailWord_990263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990283 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 5]
def baseStart_990283 : Nat := 118140960795 + 990283 * 2 ^ 59
def prefixEnd_990283 : Nat := 4983230072969 + 3 ^ 40 * 990283 * 2
def baseEnd_990283 : Nat := 508491162976454246908277

theorem tailTrace_990283 : CollatzResearch.WordTrace tailWord_990283 prefixEnd_990283 508491162976454246908277 := by
  unfold tailWord_990283
  simp only [CollatzResearch.WordTrace]
  refine ⟨36118588271381292716631503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24079058847587528477754335 36118588271381292716631503)
  ·
    refine ⟨54177882407071939074947255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36118588271381292716631503 54177882407071939074947255)
    ·
      refine ⟨81266823610607908612420883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54177882407071939074947255 81266823610607908612420883)
      ·
        refine ⟨121900235415911862918631325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81266823610607908612420883 121900235415911862918631325)
        ·
          refine ⟨45712588280966948594486747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121900235415911862918631325 45712588280966948594486747)
          ·
            refine ⟨68568882421450422891730121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45712588280966948594486747 68568882421450422891730121)
            ·
              refine ⟨51426661816087817168797591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68568882421450422891730121 51426661816087817168797591)
              ·
                refine ⟨77139992724131725753196387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51426661816087817168797591 77139992724131725753196387)
                ·
                  refine ⟨115709989086197588629794581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77139992724131725753196387 115709989086197588629794581)
                  ·
                    refine ⟨5423905738415511967021621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 115709989086197588629794581 5423905738415511967021621)
                    ·
                      refine ⟨508491162976454246908277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5423905738415511967021621 508491162976454246908277)
                      ·
                        rfl

theorem cell23_990283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 5].length) (baseStart_990283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990283 prefixEnd_990283 := by exact prefixLift 990283
  have htrace : WordTrace (prefixWord ++ tailWord_990283) baseStart_990283 baseEnd_990283 := by
    simpa [prefixWord, tailWord_990283, baseEnd_990283] using wordTrace_append hprefix tailTrace_990283
  have hstable : (prefixWord ++ tailWord_990283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990283).length < 2 ^ (prefixWord ++ tailWord_990283).sum := by decide
  have hdescent : baseEnd_990283 < baseStart_990283 := by decide
  rcases family_descends (prefixWord ++ tailWord_990283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990320 : List Nat := [2, 1, 1, 1, 5, 1, 2, 3, 1, 6]
def baseStart_990320 : Nat := 118140960795 + 990320 * 2 ^ 59
def prefixEnd_990320 : Nat := 4983230072969 + 3 ^ 40 * 990320 * 2
def baseEnd_990320 : Nat := 169503387253556867381869

theorem tailTrace_990320 : CollatzResearch.WordTrace tailWord_990320 prefixEnd_990320 169503387253556867381869 := by
  unfold tailWord_990320
  simp only [CollatzResearch.WordTrace]
  refine ⟨18059968886123624017864207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24079958514831498690485609 18059968886123624017864207)
  ·
    refine ⟨27089953329185436026796311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18059968886123624017864207 27089953329185436026796311)
    ·
      refine ⟨40634929993778154040194467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27089953329185436026796311 40634929993778154040194467)
      ·
        refine ⟨60952394990667231060291701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40634929993778154040194467 60952394990667231060291701)
        ·
          refine ⟨5714287030375052911902347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60952394990667231060291701 5714287030375052911902347)
          ·
            refine ⟨8571430545562579367853521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5714287030375052911902347 8571430545562579367853521)
            ·
              refine ⟨6428572909171934525890141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8571430545562579367853521 6428572909171934525890141)
              ·
                refine ⟨2410714840939475447208803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6428572909171934525890141 2410714840939475447208803)
                ·
                  refine ⟨3616072261409213170813205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2410714840939475447208803 3616072261409213170813205)
                  ·
                    refine ⟨169503387253556867381869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3616072261409213170813205 169503387253556867381869)
                    ·
                      rfl

theorem cell23_990320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 1, 6].length) (baseStart_990320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990320 prefixEnd_990320 := by exact prefixLift 990320
  have htrace : WordTrace (prefixWord ++ tailWord_990320) baseStart_990320 baseEnd_990320 := by
    simpa [prefixWord, tailWord_990320, baseEnd_990320] using wordTrace_append hprefix tailTrace_990320
  have hstable : (prefixWord ++ tailWord_990320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990320).length < 2 ^ (prefixWord ++ tailWord_990320).sum := by decide
  have hdescent : baseEnd_990320 < baseStart_990320 := by decide
  rcases family_descends (prefixWord ++ tailWord_990320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990337 : List Nat := [1, 2, 4, 2, 2, 2, 1, 2, 1, 6]
def baseStart_990337 : Nat := 118140960795 + 990337 * 2 ^ 59
def prefixEnd_990337 : Nat := 4983230072969 + 3 ^ 40 * 990337 * 2
def baseEnd_990337 : Nat := 169506296977265678544343

theorem tailTrace_990337 : CollatzResearch.WordTrace tailWord_990337 prefixEnd_990337 169506296977265678544343 := by
  unfold tailWord_990337
  simp only [CollatzResearch.WordTrace]
  refine ⟨36120557813185659939097265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24080371875457106626064843 36120557813185659939097265)
  ·
    refine ⟨27090418359889244954322949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36120557813185659939097265 27090418359889244954322949)
    ·
      refine ⟨5079453442479233428935553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27090418359889244954322949 5079453442479233428935553)
      ·
        refine ⟨3809590081859425071701665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5079453442479233428935553 3809590081859425071701665)
        ·
          refine ⟨2857192561394568803776249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3809590081859425071701665 2857192561394568803776249)
          ·
            refine ⟨2142894421045926602832187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2857192561394568803776249 2142894421045926602832187)
            ·
              refine ⟨3214341631568889904248281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2142894421045926602832187 3214341631568889904248281)
              ·
                refine ⟨2410756223676667428186211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3214341631568889904248281 2410756223676667428186211)
                ·
                  refine ⟨3616134335515001142279317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2410756223676667428186211 3616134335515001142279317)
                  ·
                    refine ⟨169506296977265678544343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3616134335515001142279317 169506296977265678544343)
                    ·
                      rfl

theorem cell23_990337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_990337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990337 prefixEnd_990337 := by exact prefixLift 990337
  have htrace : WordTrace (prefixWord ++ tailWord_990337) baseStart_990337 baseEnd_990337 := by
    simpa [prefixWord, tailWord_990337, baseEnd_990337] using wordTrace_append hprefix tailTrace_990337
  have hstable : (prefixWord ++ tailWord_990337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990337).length < 2 ^ (prefixWord ++ tailWord_990337).sum := by decide
  have hdescent : baseEnd_990337 < baseStart_990337 := by decide
  rcases family_descends (prefixWord ++ tailWord_990337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990347 : List Nat := [1, 1, 1, 1, 4, 1, 1, 7, 1, 2, 3]
def baseStart_990347 : Nat := 118140960795 + 990347 * 2 ^ 59
def prefixEnd_990347 : Nat := 4983230072969 + 3 ^ 40 * 990347 * 2
def baseEnd_990347 : Nat := 508524025738341996507983

theorem tailTrace_990347 : CollatzResearch.WordTrace tailWord_990347 prefixEnd_990347 508524025738341996507983 := by
  unfold tailWord_990347
  simp only [CollatzResearch.WordTrace]
  refine ⟨36120922543149431646961295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24080615028766287764640863 36120922543149431646961295)
  ·
    refine ⟨54181383814724147470441943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36120922543149431646961295 54181383814724147470441943)
    ·
      refine ⟨81272075722086221205662915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54181383814724147470441943 81272075722086221205662915)
      ·
        refine ⟨121908113583129331808494373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81272075722086221205662915 121908113583129331808494373)
        ·
          refine ⟨22857771296836749714092695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121908113583129331808494373 22857771296836749714092695)
          ·
            refine ⟨34286656945255124571139043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22857771296836749714092695 34286656945255124571139043)
            ·
              refine ⟨51429985417882686856708565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34286656945255124571139043 51429985417882686856708565)
              ·
                refine ⟨1205390283231625473204107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 51429985417882686856708565 1205390283231625473204107)
                ·
                  refine ⟨1808085424847438209806161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1205390283231625473204107 1808085424847438209806161)
                  ·
                    refine ⟨1356064068635578657354621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1808085424847438209806161 1356064068635578657354621)
                    ·
                      refine ⟨508524025738341996507983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1356064068635578657354621 508524025738341996507983)
                      ·
                        rfl

theorem cell23_990347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 7, 1, 2, 3].length) (baseStart_990347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990347 prefixEnd_990347 := by exact prefixLift 990347
  have htrace : WordTrace (prefixWord ++ tailWord_990347) baseStart_990347 baseEnd_990347 := by
    simpa [prefixWord, tailWord_990347, baseEnd_990347] using wordTrace_append hprefix tailTrace_990347
  have hstable : (prefixWord ++ tailWord_990347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990347).length < 2 ^ (prefixWord ++ tailWord_990347).sum := by decide
  have hdescent : baseEnd_990347 < baseStart_990347 := by decide
  rcases family_descends (prefixWord ++ tailWord_990347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990350 : List Nat := [4, 1, 1, 3, 2, 12]
def baseStart_990350 : Nat := 118140960795 + 990350 * 2 ^ 59
def prefixEnd_990350 : Nat := 4983230072969 + 3 ^ 40 * 990350 * 2
def baseEnd_990350 : Nat := 2092697803211133682183

theorem tailTrace_990350 : CollatzResearch.WordTrace tailWord_990350 prefixEnd_990350 2092697803211133682183 := by
  unfold tailWord_990350
  simp only [CollatzResearch.WordTrace]
  refine ⟨4515128995267320394915063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24080687974759042106213669 4515128995267320394915063)
  ·
    refine ⟨6772693492900980592372595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4515128995267320394915063 6772693492900980592372595)
    ·
      refine ⟨10159040239351470888558893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6772693492900980592372595 10159040239351470888558893)
      ·
        refine ⟨3809640089756801583209585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10159040239351470888558893 3809640089756801583209585)
        ·
          refine ⟨2857230067317601187407189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3809640089756801583209585 2857230067317601187407189)
          ·
            refine ⟨2092697803211133682183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 2857230067317601187407189 2092697803211133682183)
            ·
              rfl

theorem cell23_990350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 12].length) (baseStart_990350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990350 prefixEnd_990350 := by exact prefixLift 990350
  have htrace : WordTrace (prefixWord ++ tailWord_990350) baseStart_990350 baseEnd_990350 := by
    simpa [prefixWord, tailWord_990350, baseEnd_990350] using wordTrace_append hprefix tailTrace_990350
  have hstable : (prefixWord ++ tailWord_990350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990350).length < 2 ^ (prefixWord ++ tailWord_990350).sum := by decide
  have hdescent : baseEnd_990350 < baseStart_990350 := by decide
  rcases family_descends (prefixWord ++ tailWord_990350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990354 : List Nat := [3, 2, 3, 1, 1, 2, 1, 4, 2, 4]
def baseStart_990354 : Nat := 118140960795 + 990354 * 2 ^ 59
def prefixEnd_990354 : Nat := 4983230072969 + 3 ^ 40 * 990354 * 2
def baseEnd_990354 : Nat := 169509206700974489706817

theorem tailTrace_990354 : CollatzResearch.WordTrace tailWord_990354 prefixEnd_990354 169509206700974489706817 := by
  unfold tailWord_990354
  simp only [CollatzResearch.WordTrace]
  refine ⟨9030294463531017960616529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24080785236082714561644077 9030294463531017960616529)
  ·
    refine ⟨6772720847648263470462397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9030294463531017960616529 6772720847648263470462397)
    ·
      refine ⟨2539770317868098801423399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6772720847648263470462397 2539770317868098801423399)
      ·
        refine ⟨3809655476802148202135099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2539770317868098801423399 3809655476802148202135099)
        ·
          refine ⟨5714483215203222303202649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3809655476802148202135099 5714483215203222303202649)
          ·
            refine ⟨4285862411402416727401987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5714483215203222303202649 4285862411402416727401987)
            ·
              refine ⟨6428793617103625091102981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4285862411402416727401987 6428793617103625091102981)
              ·
                refine ⟨1205398803206929704581809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6428793617103625091102981 1205398803206929704581809)
                ·
                  refine ⟨904049102405197278436357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1205398803206929704581809 904049102405197278436357)
                  ·
                    refine ⟨169509206700974489706817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 904049102405197278436357 169509206700974489706817)
                    ·
                      rfl

theorem cell23_990354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_990354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990354 prefixEnd_990354 := by exact prefixLift 990354
  have htrace : WordTrace (prefixWord ++ tailWord_990354) baseStart_990354 baseEnd_990354 := by
    simpa [prefixWord, tailWord_990354, baseEnd_990354] using wordTrace_append hprefix tailTrace_990354
  have hstable : (prefixWord ++ tailWord_990354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990354).length < 2 ^ (prefixWord ++ tailWord_990354).sum := by decide
  have hdescent : baseEnd_990354 < baseStart_990354 := by decide
  rcases family_descends (prefixWord ++ tailWord_990354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990378 : List Nat := [3, 1, 5, 1, 1, 2, 1, 2, 3, 2, 2]
def baseStart_990378 : Nat := 118140960795 + 990378 * 2 ^ 59
def prefixEnd_990378 : Nat := 4983230072969 + 3 ^ 40 * 990378 * 2
def baseEnd_990378 : Nat := 508539943638631375220341

theorem tailTrace_990378 : CollatzResearch.WordTrace tailWord_990378 prefixEnd_990378 508539943638631375220341 := by
  unfold tailWord_990378
  simp only [CollatzResearch.WordTrace]
  refine ⟨9030513301509280985334947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24081368804024749294226525 9030513301509280985334947)
  ·
    refine ⟨13545769952263921478002421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9030513301509280985334947 13545769952263921478002421)
    ·
      refine ⟨1269915933024742638562727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13545769952263921478002421 1269915933024742638562727)
      ·
        refine ⟨1904873899537113957844091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1269915933024742638562727 1904873899537113957844091)
        ·
          refine ⟨2857310849305670936766137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1904873899537113957844091 2857310849305670936766137)
          ·
            refine ⟨2142983136979253202574603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2857310849305670936766137 2142983136979253202574603)
            ·
              refine ⟨3214474705468879803861905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2142983136979253202574603 3214474705468879803861905)
              ·
                refine ⟨2410856029101659852896429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3214474705468879803861905 2410856029101659852896429)
                ·
                  refine ⟨904071010913122444836161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2410856029101659852896429 904071010913122444836161)
                  ·
                    refine ⟨678053258184841833627121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 904071010913122444836161 678053258184841833627121)
                    ·
                      refine ⟨508539943638631375220341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 678053258184841833627121 508539943638631375220341)
                      ·
                        rfl

theorem cell23_990378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_990378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990378 prefixEnd_990378 := by exact prefixLift 990378
  have htrace : WordTrace (prefixWord ++ tailWord_990378) baseStart_990378 baseEnd_990378 := by
    simpa [prefixWord, tailWord_990378, baseEnd_990378] using wordTrace_append hprefix tailTrace_990378
  have hstable : (prefixWord ++ tailWord_990378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990378).length < 2 ^ (prefixWord ++ tailWord_990378).sum := by decide
  have hdescent : baseEnd_990378 < baseStart_990378 := by decide
  rcases family_descends (prefixWord ++ tailWord_990378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990398 : List Nat := [4, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3]
def baseStart_990398 : Nat := 118140960795 + 990398 * 2 ^ 59
def prefixEnd_990398 : Nat := 4983230072969 + 3 ^ 40 * 990398 * 2
def baseEnd_990398 : Nat := 508550213251721296970249

theorem tailTrace_990398 : CollatzResearch.WordTrace tailWord_990398 prefixEnd_990398 508550213251721296970249 := by
  unfold tailWord_990398
  simp only [CollatzResearch.WordTrace]
  refine ⟨4515347833245583419633481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24081855110643111571378565 4515347833245583419633481)
  ·
    refine ⟨3386510874934187564725111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4515347833245583419633481 3386510874934187564725111)
    ·
      refine ⟨5079766312401281347087667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3386510874934187564725111 5079766312401281347087667)
      ·
        refine ⟨7619649468601922020631501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5079766312401281347087667 7619649468601922020631501)
        ·
          refine ⟨2857368550725720757736813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7619649468601922020631501 2857368550725720757736813)
          ·
            refine ⟨1071513206522145284151305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2857368550725720757736813 1071513206522145284151305)
            ·
              refine ⟨803634904891608963113479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1071513206522145284151305 803634904891608963113479)
              ·
                refine ⟨1205452357337413444670219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 803634904891608963113479 1205452357337413444670219)
                ·
                  refine ⟨1808178536006120167005329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1205452357337413444670219 1808178536006120167005329)
                  ·
                    refine ⟨1356133902004590125253997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1808178536006120167005329 1356133902004590125253997)
                    ·
                      refine ⟨508550213251721296970249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1356133902004590125253997 508550213251721296970249)
                      ·
                        rfl

theorem cell23_990398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3].length) (baseStart_990398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990398 prefixEnd_990398 := by exact prefixLift 990398
  have htrace : WordTrace (prefixWord ++ tailWord_990398) baseStart_990398 baseEnd_990398 := by
    simpa [prefixWord, tailWord_990398, baseEnd_990398] using wordTrace_append hprefix tailTrace_990398
  have hstable : (prefixWord ++ tailWord_990398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990398).length < 2 ^ (prefixWord ++ tailWord_990398).sum := by decide
  have hdescent : baseEnd_990398 < baseStart_990398 := by decide
  rcases family_descends (prefixWord ++ tailWord_990398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990487 : List Nat := [1, 1, 3, 4, 1, 1, 1, 2, 4, 5]
def baseStart_990487 : Nat := 118140960795 + 990487 * 2 ^ 59
def prefixEnd_990487 : Nat := 4983230072969 + 3 ^ 40 * 990487 * 2
def baseEnd_990487 : Nat := 169531971009990482919113

theorem tailTrace_990487 : CollatzResearch.WordTrace tailWord_990487 prefixEnd_990487 169531971009990482919113 := by
  unfold tailWord_990487
  simp only [CollatzResearch.WordTrace]
  refine ⟨36126028762642235557057715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24084019175094823704705143 36126028762642235557057715)
  ·
    refine ⟨54189043143963353335586573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36126028762642235557057715 54189043143963353335586573)
    ·
      refine ⟨20320891178986257500844965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54189043143963353335586573 20320891178986257500844965)
      ·
        refine ⟨3810167096059923281408431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20320891178986257500844965 3810167096059923281408431)
        ·
          refine ⟨5715250644089884922112647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3810167096059923281408431 5715250644089884922112647)
          ·
            refine ⟨8572875966134827383168971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5715250644089884922112647 8572875966134827383168971)
            ·
              refine ⟨12859313949202241074753457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8572875966134827383168971 12859313949202241074753457)
              ·
                refine ⟨9644485461901680806065093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12859313949202241074753457 9644485461901680806065093)
                ·
                  refine ⟨1808341024106565151137205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9644485461901680806065093 1808341024106565151137205)
                  ·
                    refine ⟨169531971009990482919113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1808341024106565151137205 169531971009990482919113)
                    ·
                      rfl

theorem cell23_990487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 4, 5].length) (baseStart_990487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990487 prefixEnd_990487 := by exact prefixLift 990487
  have htrace : WordTrace (prefixWord ++ tailWord_990487) baseStart_990487 baseEnd_990487 := by
    simpa [prefixWord, tailWord_990487, baseEnd_990487] using wordTrace_append hprefix tailTrace_990487
  have hstable : (prefixWord ++ tailWord_990487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990487).length < 2 ^ (prefixWord ++ tailWord_990487).sum := by decide
  have hdescent : baseEnd_990487 < baseStart_990487 := by decide
  rcases family_descends (prefixWord ++ tailWord_990487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990504 : List Nat := [2, 1, 5, 1, 2, 1, 1, 3, 2, 5]
def baseStart_990504 : Nat := 118140960795 + 990504 * 2 ^ 59
def prefixEnd_990504 : Nat := 4983230072969 + 3 ^ 40 * 990504 * 2
def baseEnd_990504 : Nat := 169534880733699294081587

theorem tailTrace_990504 : CollatzResearch.WordTrace tailWord_990504 prefixEnd_990504 169534880733699294081587 := by
  unfold tailWord_990504
  simp only [CollatzResearch.WordTrace]
  refine ⟨18063324401790323730213283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24084432535720431640284377 18063324401790323730213283)
  ·
    refine ⟨27094986602685485595319925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18063324401790323730213283 27094986602685485595319925)
    ·
      refine ⟨2540154994001764274561243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27094986602685485595319925 2540154994001764274561243)
      ·
        refine ⟨3810232491002646411841865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2540154994001764274561243 3810232491002646411841865)
        ·
          refine ⟨2857674368251984808881399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3810232491002646411841865 2857674368251984808881399)
          ·
            refine ⟨4286511552377977213322099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2857674368251984808881399 4286511552377977213322099)
            ·
              refine ⟨6429767328566965819983149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4286511552377977213322099 6429767328566965819983149)
              ·
                refine ⟨2411162748212612182493681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6429767328566965819983149 2411162748212612182493681)
                ·
                  refine ⟨1808372061159459136870261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2411162748212612182493681 1808372061159459136870261)
                  ·
                    refine ⟨169534880733699294081587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1808372061159459136870261 169534880733699294081587)
                    ·
                      rfl

theorem cell23_990504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_990504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990504 prefixEnd_990504 := by exact prefixLift 990504
  have htrace : WordTrace (prefixWord ++ tailWord_990504) baseStart_990504 baseEnd_990504 := by
    simpa [prefixWord, tailWord_990504, baseEnd_990504] using wordTrace_append hprefix tailTrace_990504
  have hstable : (prefixWord ++ tailWord_990504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990504).length < 2 ^ (prefixWord ++ tailWord_990504).sum := by decide
  have hdescent : baseEnd_990504 < baseStart_990504 := by decide
  rcases family_descends (prefixWord ++ tailWord_990504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990524 : List Nat := [2, 2, 2, 2, 1, 3, 2, 2, 2, 1, 4]
def baseStart_990524 : Nat := 118140960795 + 990524 * 2 ^ 59
def prefixEnd_990524 : Nat := 4983230072969 + 3 ^ 40 * 990524 * 2
def baseEnd_990524 : Nat := 508614911814187803994669

theorem tailTrace_990524 : CollatzResearch.WordTrace tailWord_990524 prefixEnd_990524 508614911814187803994669 := by
  unfold tailWord_990524
  simp only [CollatzResearch.WordTrace]
  refine ⟨18063689131754095438077313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24084918842338793917436417 18063689131754095438077313)
  ·
    refine ⟨13547766848815571578557985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18063689131754095438077313 13547766848815571578557985)
    ·
      refine ⟨10160825136611678683918489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13547766848815571578557985 10160825136611678683918489)
      ·
        refine ⟨7620618852458759012938867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10160825136611678683918489 7620618852458759012938867)
        ·
          refine ⟨11430928278688138519408301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7620618852458759012938867 11430928278688138519408301)
          ·
            refine ⟨4286598104508051944778113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11430928278688138519408301 4286598104508051944778113)
            ·
              refine ⟨3214948578381038958583585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4286598104508051944778113 3214948578381038958583585)
              ·
                refine ⟨2411211433785779218937689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3214948578381038958583585 2411211433785779218937689)
                ·
                  refine ⟨1808408575339334414203267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2411211433785779218937689 1808408575339334414203267)
                  ·
                    refine ⟨2712612863009001621304901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1808408575339334414203267 2712612863009001621304901)
                    ·
                      refine ⟨508614911814187803994669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2712612863009001621304901 508614911814187803994669)
                      ·
                        rfl

theorem cell23_990524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_990524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990524 prefixEnd_990524 := by exact prefixLift 990524
  have htrace : WordTrace (prefixWord ++ tailWord_990524) baseStart_990524 baseEnd_990524 := by
    simpa [prefixWord, tailWord_990524, baseEnd_990524] using wordTrace_append hprefix tailTrace_990524
  have hstable : (prefixWord ++ tailWord_990524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990524).length < 2 ^ (prefixWord ++ tailWord_990524).sum := by decide
  have hdescent : baseEnd_990524 < baseStart_990524 := by decide
  rcases family_descends (prefixWord ++ tailWord_990524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990525 : List Nat := [1, 4, 1, 5, 1, 2, 2, 2, 5]
def baseStart_990525 : Nat := 118140960795 + 990525 * 2 ^ 59
def prefixEnd_990525 : Nat := 4983230072969 + 3 ^ 40 * 990525 * 2
def baseEnd_990525 : Nat := 56512825032760255564685

theorem tailTrace_990525 : CollatzResearch.WordTrace tailWord_990525 prefixEnd_990525 56512825032760255564685 := by
  unfold tailWord_990525
  simp only [CollatzResearch.WordTrace]
  refine ⟨36127414736504568046941029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24084943157669712031294019 36127414736504568046941029)
  ·
    refine ⟨6773890263094606508801443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36127414736504568046941029 6773890263094606508801443)
    ·
      refine ⟨10160835394641909763202165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6773890263094606508801443 10160835394641909763202165)
      ·
        refine ⟨952578318247679040300203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10160835394641909763202165 952578318247679040300203)
        ·
          refine ⟨1428867477371518560450305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 952578318247679040300203 1428867477371518560450305)
          ·
            refine ⟨1071650608028638920337729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1428867477371518560450305 1071650608028638920337729)
            ·
              refine ⟨803737956021479190253297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1071650608028638920337729 803737956021479190253297)
              ·
                refine ⟨602803467016109392689973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 803737956021479190253297 602803467016109392689973)
                ·
                  refine ⟨56512825032760255564685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 602803467016109392689973 56512825032760255564685)
                  ·
                    rfl

theorem cell23_990525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 2, 5].length) (baseStart_990525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990525 prefixEnd_990525 := by exact prefixLift 990525
  have htrace : WordTrace (prefixWord ++ tailWord_990525) baseStart_990525 baseEnd_990525 := by
    simpa [prefixWord, tailWord_990525, baseEnd_990525] using wordTrace_append hprefix tailTrace_990525
  have hstable : (prefixWord ++ tailWord_990525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990525).length < 2 ^ (prefixWord ++ tailWord_990525).sum := by decide
  have hdescent : baseEnd_990525 < baseStart_990525 := by decide
  rcases family_descends (prefixWord ++ tailWord_990525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990547 : List Nat := [1, 1, 1, 2, 1, 1, 5, 5, 6]
def baseStart_990547 : Nat := 118140960795 + 990547 * 2 ^ 59
def prefixEnd_990547 : Nat := 4983230072969 + 3 ^ 40 * 990547 * 2
def baseEnd_990547 : Nat := 56514080207693468223007

theorem tailTrace_990547 : CollatzResearch.WordTrace tailWord_990547 prefixEnd_990547 56514080207693468223007 := by
  unfold tailWord_990547
  simp only [CollatzResearch.WordTrace]
  refine ⟨36128217142424865804241895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24085478094949910536161263 36128217142424865804241895)
  ·
    refine ⟨54192325713637298706362843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36128217142424865804241895 54192325713637298706362843)
    ·
      refine ⟨81288488570455948059544265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54192325713637298706362843 81288488570455948059544265)
      ·
        refine ⟨60966366427841961044658199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81288488570455948059544265 60966366427841961044658199)
        ·
          refine ⟨91449549641762941566987299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60966366427841961044658199 91449549641762941566987299)
          ·
            refine ⟨137174324462644412350480949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91449549641762941566987299 137174324462644412350480949)
            ·
              refine ⟨12860092918372913657857589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137174324462644412350480949 12860092918372913657857589)
              ·
                refine ⟨1205633711097460655424149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12860092918372913657857589 1205633711097460655424149)
                ·
                  refine ⟨56514080207693468223007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1205633711097460655424149 56514080207693468223007)
                  ·
                    rfl

theorem cell23_990547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 5, 6].length) (baseStart_990547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990547 prefixEnd_990547 := by exact prefixLift 990547
  have htrace : WordTrace (prefixWord ++ tailWord_990547) baseStart_990547 baseEnd_990547 := by
    simpa [prefixWord, tailWord_990547, baseEnd_990547] using wordTrace_append hprefix tailTrace_990547
  have hstable : (prefixWord ++ tailWord_990547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990547).length < 2 ^ (prefixWord ++ tailWord_990547).sum := by decide
  have hdescent : baseEnd_990547 < baseStart_990547 := by decide
  rcases family_descends (prefixWord ++ tailWord_990547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990624 : List Nat := [2, 1, 1, 4, 1, 2, 1, 1, 6, 4]
def baseStart_990624 : Nat := 118140960795 + 990624 * 2 ^ 59
def prefixEnd_990624 : Nat := 4983230072969 + 3 ^ 40 * 990624 * 2
def baseEnd_990624 : Nat := 169555419959879137581403

theorem tailTrace_990624 : CollatzResearch.WordTrace tailWord_990624 prefixEnd_990624 169555419959879137581403 := by
  unfold tailWord_990624
  simp only [CollatzResearch.WordTrace]
  refine ⟨18065512781572953977397463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24087350375430605303196617 18065512781572953977397463)
  ·
    refine ⟨27098269172359430966096195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18065512781572953977397463 27098269172359430966096195)
    ·
      refine ⟨40647403758539146449144293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27098269172359430966096195 40647403758539146449144293)
      ·
        refine ⟨7621388204726089959214555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40647403758539146449144293 7621388204726089959214555)
        ·
          refine ⟨11432082307089134938821833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7621388204726089959214555 11432082307089134938821833)
          ·
            refine ⟨8574061730316851204116375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11432082307089134938821833 8574061730316851204116375)
            ·
              refine ⟨12861092595475276806174563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8574061730316851204116375 12861092595475276806174563)
              ·
                refine ⟨19291638893212915209261845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12861092595475276806174563 19291638893212915209261845)
                ·
                  refine ⟨904295573119355400434149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 19291638893212915209261845 904295573119355400434149)
                  ·
                    refine ⟨169555419959879137581403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 904295573119355400434149 169555419959879137581403)
                    ·
                      rfl

theorem cell23_990624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 6, 4].length) (baseStart_990624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990624 prefixEnd_990624 := by exact prefixLift 990624
  have htrace : WordTrace (prefixWord ++ tailWord_990624) baseStart_990624 baseEnd_990624 := by
    simpa [prefixWord, tailWord_990624, baseEnd_990624] using wordTrace_append hprefix tailTrace_990624
  have hstable : (prefixWord ++ tailWord_990624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990624).length < 2 ^ (prefixWord ++ tailWord_990624).sum := by decide
  have hdescent : baseEnd_990624 < baseStart_990624 := by decide
  rcases family_descends (prefixWord ++ tailWord_990624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990631 : List Nat := [1, 1, 6, 1, 1, 1, 1, 5, 1, 1, 4]
def baseStart_990631 : Nat := 118140960795 + 990631 * 2 ^ 59
def prefixEnd_990631 : Nat := 4983230072969 + 3 ^ 40 * 990631 * 2
def baseEnd_990631 : Nat := 508669854244218885356677

theorem tailTrace_990631 : CollatzResearch.WordTrace tailWord_990631 prefixEnd_990631 508669854244218885356677 := by
  unfold tailWord_990631
  simp only [CollatzResearch.WordTrace]
  refine ⟨36131280874120548150299747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24087520582747032100199831 36131280874120548150299747)
  ·
    refine ⟨54196921311180822225449621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36131280874120548150299747 54196921311180822225449621)
    ·
      refine ⟨2540480686461601041817951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 54196921311180822225449621 2540480686461601041817951)
      ·
        refine ⟨3810721029692401562726927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2540480686461601041817951 3810721029692401562726927)
        ·
          refine ⟨5716081544538602344090391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3810721029692401562726927 5716081544538602344090391)
          ·
            refine ⟨8574122316807903516135587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5716081544538602344090391 8574122316807903516135587)
            ·
              refine ⟨12861183475211855274203381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8574122316807903516135587 12861183475211855274203381)
              ·
                refine ⟨1205735950801111431956567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12861183475211855274203381 1205735950801111431956567)
                ·
                  refine ⟨1808603926201667147934851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1205735950801111431956567 1808603926201667147934851)
                  ·
                    refine ⟨2712905889302500721902277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1808603926201667147934851 2712905889302500721902277)
                    ·
                      refine ⟨508669854244218885356677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2712905889302500721902277 508669854244218885356677)
                      ·
                        rfl

theorem cell23_990631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_990631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990631 prefixEnd_990631 := by exact prefixLift 990631
  have htrace : WordTrace (prefixWord ++ tailWord_990631) baseStart_990631 baseEnd_990631 := by
    simpa [prefixWord, tailWord_990631, baseEnd_990631] using wordTrace_append hprefix tailTrace_990631
  have hstable : (prefixWord ++ tailWord_990631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990631).length < 2 ^ (prefixWord ++ tailWord_990631).sum := by decide
  have hdescent : baseEnd_990631 < baseStart_990631 := by decide
  rcases family_descends (prefixWord ++ tailWord_990631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990641 : List Nat := [1, 2, 2, 4, 1, 1, 2, 4, 2, 4]
def baseStart_990641 : Nat := 118140960795 + 990641 * 2 ^ 59
def prefixEnd_990641 : Nat := 4983230072969 + 3 ^ 40 * 990641 * 2
def baseEnd_990641 : Nat := 169558329683587948743877

theorem tailTrace_990641 : CollatzResearch.WordTrace tailWord_990641 prefixEnd_990641 169558329683587948743877 := by
  unfold tailWord_990641
  simp only [CollatzResearch.WordTrace]
  refine ⟨36131645604084319858163777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24087763736056213238775851 36131645604084319858163777)
  ·
    refine ⟨27098734203063239893622833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36131645604084319858163777 27098734203063239893622833)
    ·
      refine ⟨20324050652297429920217125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27098734203063239893622833 20324050652297429920217125)
      ·
        refine ⟨3810759497305768110040711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20324050652297429920217125 3810759497305768110040711)
        ·
          refine ⟨5716139245958652165061067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3810759497305768110040711 5716139245958652165061067)
          ·
            refine ⟨8574208868937978247591601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5716139245958652165061067 8574208868937978247591601)
            ·
              refine ⟨6430656651703483685693701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8574208868937978247591601 6430656651703483685693701)
              ·
                refine ⟨1205748122194403191067569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6430656651703483685693701 1205748122194403191067569)
                ·
                  refine ⟨904311091645802393300677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1205748122194403191067569 904311091645802393300677)
                  ·
                    refine ⟨169558329683587948743877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 904311091645802393300677 169558329683587948743877)
                    ·
                      rfl

theorem cell23_990641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 4, 2, 4].length) (baseStart_990641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990641 prefixEnd_990641 := by exact prefixLift 990641
  have htrace : WordTrace (prefixWord ++ tailWord_990641) baseStart_990641 baseEnd_990641 := by
    simpa [prefixWord, tailWord_990641, baseEnd_990641] using wordTrace_append hprefix tailTrace_990641
  have hstable : (prefixWord ++ tailWord_990641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990641).length < 2 ^ (prefixWord ++ tailWord_990641).sum := by decide
  have hdescent : baseEnd_990641 < baseStart_990641 := by decide
  rcases family_descends (prefixWord ++ tailWord_990641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990648 : List Nat := [2, 1, 2, 1, 2, 2, 5, 1, 3, 2, 2]
def baseStart_990648 : Nat := 118140960795 + 990648 * 2 ^ 59
def prefixEnd_990648 : Nat := 4983230072969 + 3 ^ 40 * 990648 * 2
def baseEnd_990648 : Nat := 508678583415345318844099

theorem tailTrace_990648 : CollatzResearch.WordTrace tailWord_990648 prefixEnd_990648 508678583415345318844099 := by
  unfold tailWord_990648
  simp only [CollatzResearch.WordTrace]
  refine ⟨18065950457529480026834299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24087933943372640035779065 18065950457529480026834299)
  ·
    refine ⟨27098925686294220040251449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18065950457529480026834299 27098925686294220040251449)
    ·
      refine ⟨20324194264720665030188587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27098925686294220040251449 20324194264720665030188587)
      ·
        refine ⟨30486291397080997545282881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20324194264720665030188587 30486291397080997545282881)
        ·
          refine ⟨22864718547810748158962161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30486291397080997545282881 22864718547810748158962161)
          ·
            refine ⟨17148538910858061119221621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22864718547810748158962161 17148538910858061119221621)
            ·
              refine ⟨1607675522892943229927027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17148538910858061119221621 1607675522892943229927027)
              ·
                refine ⟨2411513284339414844890541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1607675522892943229927027 2411513284339414844890541)
                ·
                  refine ⟨904317481627280566833953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2411513284339414844890541 904317481627280566833953)
                  ·
                    refine ⟨678238111220460425125465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 904317481627280566833953 678238111220460425125465)
                    ·
                      refine ⟨508678583415345318844099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 678238111220460425125465 508678583415345318844099)
                      ·
                        rfl

theorem cell23_990648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 3, 2, 2].length) (baseStart_990648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990648 prefixEnd_990648 := by exact prefixLift 990648
  have htrace : WordTrace (prefixWord ++ tailWord_990648) baseStart_990648 baseEnd_990648 := by
    simpa [prefixWord, tailWord_990648, baseEnd_990648] using wordTrace_append hprefix tailTrace_990648
  have hstable : (prefixWord ++ tailWord_990648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990648).length < 2 ^ (prefixWord ++ tailWord_990648).sum := by decide
  have hdescent : baseEnd_990648 < baseStart_990648 := by decide
  rcases family_descends (prefixWord ++ tailWord_990648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990668 : List Nat := [2, 2, 1, 4, 2, 1, 3, 2, 1, 2, 3]
def baseStart_990668 : Nat := 118140960795 + 990668 * 2 ^ 59
def prefixEnd_990668 : Nat := 4983230072969 + 3 ^ 40 * 990668 * 2
def baseEnd_990668 : Nat := 508688853028435240594007

theorem tailTrace_990668 : CollatzResearch.WordTrace tailWord_990668 prefixEnd_990668 508688853028435240594007 := by
  unfold tailWord_990668
  simp only [CollatzResearch.WordTrace]
  refine ⟨18066315187493251734698329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24088420249991002312931105 18066315187493251734698329)
  ·
    refine ⟨13549736390619938801023747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18066315187493251734698329 13549736390619938801023747)
    ·
      refine ⟨20324604585929908201535621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13549736390619938801023747 20324604585929908201535621)
      ·
        refine ⟨3810863359861857787787929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20324604585929908201535621 3810863359861857787787929)
        ·
          refine ⟨2858147519896393340840947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3810863359861857787787929 2858147519896393340840947)
          ·
            refine ⟨4287221279844590011261421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2858147519896393340840947 4287221279844590011261421)
            ·
              refine ⟨1607707979941721254223033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4287221279844590011261421 1607707979941721254223033)
              ·
                refine ⟨1205780984956290940667275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1607707979941721254223033 1205780984956290940667275)
                ·
                  refine ⟨1808671477434436411000913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1205780984956290940667275 1808671477434436411000913)
                  ·
                    refine ⟨1356503608075827308250685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1808671477434436411000913 1356503608075827308250685)
                    ·
                      refine ⟨508688853028435240594007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1356503608075827308250685 508688853028435240594007)
                      ·
                        rfl

theorem cell23_990668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_990668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990668 prefixEnd_990668 := by exact prefixLift 990668
  have htrace : WordTrace (prefixWord ++ tailWord_990668) baseStart_990668 baseEnd_990668 := by
    simpa [prefixWord, tailWord_990668, baseEnd_990668] using wordTrace_append hprefix tailTrace_990668
  have hstable : (prefixWord ++ tailWord_990668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990668).length < 2 ^ (prefixWord ++ tailWord_990668).sum := by decide
  have hdescent : baseEnd_990668 < baseStart_990668 := by decide
  rcases family_descends (prefixWord ++ tailWord_990668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990678 : List Nat := [5, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4]
def baseStart_990678 : Nat := 118140960795 + 990678 * 2 ^ 59
def prefixEnd_990678 : Nat := 4983230072969 + 3 ^ 40 * 990678 * 2
def baseEnd_990678 : Nat := 508693987834980201468961

theorem tailTrace_990678 : CollatzResearch.WordTrace tailWord_990678 prefixEnd_990678 508693987834980201468961 := by
  unfold tailWord_990678
  simp only [CollatzResearch.WordTrace]
  refine ⟨2258312194059392198578793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24088663403300183451507125 2258312194059392198578793)
  ·
    refine ⟨1693734145544544148934095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2258312194059392198578793 1693734145544544148934095)
    ·
      refine ⟨2540601218316816223401143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1693734145544544148934095 2540601218316816223401143)
      ·
        refine ⟨3810901827475224335101715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2540601218316816223401143 3810901827475224335101715)
        ·
          refine ⟨5716352741212836502652573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3810901827475224335101715 5716352741212836502652573)
          ·
            refine ⟨2143632277954813688494715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5716352741212836502652573 2143632277954813688494715)
            ·
              refine ⟨3215448416932220532742073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2143632277954813688494715 3215448416932220532742073)
              ·
                refine ⟨2411586312699165399556555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3215448416932220532742073 2411586312699165399556555)
                ·
                  refine ⟨3617379469048748099334833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2411586312699165399556555 3617379469048748099334833)
                  ·
                    refine ⟨2713034601786561074501125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3617379469048748099334833 2713034601786561074501125)
                    ·
                      refine ⟨508693987834980201468961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2713034601786561074501125 508693987834980201468961)
                      ·
                        rfl

theorem cell23_990678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_990678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990678 prefixEnd_990678 := by exact prefixLift 990678
  have htrace : WordTrace (prefixWord ++ tailWord_990678) baseStart_990678 baseEnd_990678 := by
    simpa [prefixWord, tailWord_990678, baseEnd_990678] using wordTrace_append hprefix tailTrace_990678
  have hstable : (prefixWord ++ tailWord_990678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990678).length < 2 ^ (prefixWord ++ tailWord_990678).sum := by decide
  have hdescent : baseEnd_990678 < baseStart_990678 := by decide
  rcases family_descends (prefixWord ++ tailWord_990678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990681 : List Nat := [1, 2, 1, 2, 4, 3, 1, 2, 1, 3, 3]
def baseStart_990681 : Nat := 118140960795 + 990681 * 2 ^ 59
def prefixEnd_990681 : Nat := 4983230072969 + 3 ^ 40 * 990681 * 2
def baseEnd_990681 : Nat := 508695528276943689731447

theorem tailTrace_990681 : CollatzResearch.WordTrace tailWord_990681 prefixEnd_990681 508695528276943689731447 := by
  unfold tailWord_990681
  simp only [CollatzResearch.WordTrace]
  refine ⟨36133104523939406689619897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24088736349292937793079931 36133104523939406689619897)
  ·
    refine ⟨27099828392954555017214923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36133104523939406689619897 27099828392954555017214923)
    ·
      refine ⟨40649742589431832525822385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27099828392954555017214923 40649742589431832525822385)
      ·
        refine ⟨30487306942073874394366789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40649742589431832525822385 30487306942073874394366789)
        ·
          refine ⟨5716370051638851448943773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30487306942073874394366789 5716370051638851448943773)
          ·
            refine ⟨2143638769364569293353915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5716370051638851448943773 2143638769364569293353915)
            ·
              refine ⟨3215458154046853940030873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2143638769364569293353915 3215458154046853940030873)
              ·
                refine ⟨2411593615535140455023155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3215458154046853940030873 2411593615535140455023155)
                ·
                  refine ⟨3617390423302710682534733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2411593615535140455023155 3617390423302710682534733)
                  ·
                    refine ⟨1356521408738516505950525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3617390423302710682534733 1356521408738516505950525)
                    ·
                      refine ⟨508695528276943689731447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1356521408738516505950525 508695528276943689731447)
                      ·
                        rfl

theorem cell23_990681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 3, 3].length) (baseStart_990681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990681 prefixEnd_990681 := by exact prefixLift 990681
  have htrace : WordTrace (prefixWord ++ tailWord_990681) baseStart_990681 baseEnd_990681 := by
    simpa [prefixWord, tailWord_990681, baseEnd_990681] using wordTrace_append hprefix tailTrace_990681
  have hstable : (prefixWord ++ tailWord_990681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990681).length < 2 ^ (prefixWord ++ tailWord_990681).sum := by decide
  have hdescent : baseEnd_990681 < baseStart_990681 := by decide
  rcases family_descends (prefixWord ++ tailWord_990681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990685 : List Nat := [1, 4, 3, 1, 1, 3, 3, 1, 1, 2, 3]
def baseStart_990685 : Nat := 118140960795 + 990685 * 2 ^ 59
def prefixEnd_990685 : Nat := 4983230072969 + 3 ^ 40 * 990685 * 2
def baseEnd_990685 : Nat := 508697582199561674081429

theorem tailTrace_990685 : CollatzResearch.WordTrace tailWord_990685 prefixEnd_990685 508697582199561674081429 := by
  unfold tailWord_990685
  simp only [CollatzResearch.WordTrace]
  refine ⟨36133250415924915372765509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24088833610616610248510339 36133250415924915372765509)
  ·
    refine ⟨6774984452985921632393533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36133250415924915372765509 6774984452985921632393533)
    ·
      refine ⟨2540619169869720612147575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6774984452985921632393533 2540619169869720612147575)
      ·
        refine ⟨3810928754804580918221363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2540619169869720612147575 3810928754804580918221363)
        ·
          refine ⟨5716393132206871377332045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3810928754804580918221363 5716393132206871377332045)
          ·
            refine ⟨2143647424577576766499517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5716393132206871377332045 2143647424577576766499517)
            ·
              refine ⟨803867784216591287437319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2143647424577576766499517 803867784216591287437319)
              ·
                refine ⟨1205801676324886931155979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 803867784216591287437319 1205801676324886931155979)
                ·
                  refine ⟨1808702514487330396733969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1205801676324886931155979 1808702514487330396733969)
                  ·
                    refine ⟨1356526885865497797550477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1808702514487330396733969 1356526885865497797550477)
                    ·
                      refine ⟨508697582199561674081429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1356526885865497797550477 508697582199561674081429)
                      ·
                        rfl

theorem cell23_990685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_990685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990685 prefixEnd_990685 := by exact prefixLift 990685
  have htrace : WordTrace (prefixWord ++ tailWord_990685) baseStart_990685 baseEnd_990685 := by
    simpa [prefixWord, tailWord_990685, baseEnd_990685] using wordTrace_append hprefix tailTrace_990685
  have hstable : (prefixWord ++ tailWord_990685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990685).length < 2 ^ (prefixWord ++ tailWord_990685).sum := by decide
  have hdescent : baseEnd_990685 < baseStart_990685 := by decide
  rcases family_descends (prefixWord ++ tailWord_990685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990704 : List Nat := [2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 4]
def baseStart_990704 : Nat := 118140960795 + 990704 * 2 ^ 59
def prefixEnd_990704 : Nat := 4983230072969 + 3 ^ 40 * 990704 * 2
def baseEnd_990704 : Nat := 508707338331997099743841

theorem tailTrace_990704 : CollatzResearch.WordTrace tailWord_990704 prefixEnd_990704 508707338331997099743841 := by
  unfold tailWord_990704
  simp only [CollatzResearch.WordTrace]
  refine ⟨18066971701428040808853583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24089295601904054411804777 18066971701428040808853583)
  ·
    refine ⟨27100457552142061213280375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18066971701428040808853583 27100457552142061213280375)
    ·
      refine ⟨40650686328213091819920563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27100457552142061213280375 40650686328213091819920563)
      ·
        refine ⟨60976029492319637729880845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40650686328213091819920563 60976029492319637729880845)
        ·
          refine ⟨22866011059619864148705317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60976029492319637729880845 22866011059619864148705317)
          ·
            refine ⟨4287377073678724527882247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22866011059619864148705317 4287377073678724527882247)
            ·
              refine ⟨6431065610518086791823371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4287377073678724527882247 6431065610518086791823371)
              ·
                refine ⟨9646598415777130187735057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6431065610518086791823371 9646598415777130187735057)
                ·
                  refine ⟨7234948811832847640801293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9646598415777130187735057 7234948811832847640801293)
                  ·
                    refine ⟨2713105804437317865300485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7234948811832847640801293 2713105804437317865300485)
                    ·
                      refine ⟨508707338331997099743841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2713105804437317865300485 508707338331997099743841)
                      ·
                        rfl

theorem cell23_990704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 4].length) (baseStart_990704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990704 prefixEnd_990704 := by exact prefixLift 990704
  have htrace : WordTrace (prefixWord ++ tailWord_990704) baseStart_990704 baseEnd_990704 := by
    simpa [prefixWord, tailWord_990704, baseEnd_990704] using wordTrace_append hprefix tailTrace_990704
  have hstable : (prefixWord ++ tailWord_990704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990704).length < 2 ^ (prefixWord ++ tailWord_990704).sum := by decide
  have hdescent : baseEnd_990704 < baseStart_990704 := by decide
  rcases family_descends (prefixWord ++ tailWord_990704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990714 : List Nat := [3, 1, 1, 1, 1, 2, 5, 1, 2, 6]
def baseStart_990714 : Nat := 118140960795 + 990714 * 2 ^ 59
def prefixEnd_990714 : Nat := 4983230072969 + 3 ^ 40 * 990714 * 2
def baseEnd_990714 : Nat := 169570824379514020206265

theorem tailTrace_990714 : CollatzResearch.WordTrace tailWord_990714 prefixEnd_990714 169570824379514020206265 := by
  unfold tailWord_990714
  simp only [CollatzResearch.WordTrace]
  refine ⟨9033577033204963331392799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24089538755213235550380797 9033577033204963331392799)
  ·
    refine ⟨13550365549807444997089199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9033577033204963331392799 13550365549807444997089199)
    ·
      refine ⟨20325548324711167495633799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13550365549807444997089199 20325548324711167495633799)
      ·
        refine ⟨30488322487066751243450699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20325548324711167495633799 30488322487066751243450699)
        ·
          refine ⟨45732483730600126865176049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30488322487066751243450699 45732483730600126865176049)
          ·
            refine ⟨34299362797950095148882037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45732483730600126865176049 34299362797950095148882037)
            ·
              refine ⟨3215565262307821420207691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34299362797950095148882037 3215565262307821420207691)
              ·
                refine ⟨4823347893461732130311537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3215565262307821420207691 4823347893461732130311537)
                ·
                  refine ⟨3617510920096299097733653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4823347893461732130311537 3617510920096299097733653)
                  ·
                    refine ⟨169570824379514020206265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3617510920096299097733653 169570824379514020206265)
                    ·
                      rfl

theorem cell23_990714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 2, 6].length) (baseStart_990714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990714 prefixEnd_990714 := by exact prefixLift 990714
  have htrace : WordTrace (prefixWord ++ tailWord_990714) baseStart_990714 baseEnd_990714 := by
    simpa [prefixWord, tailWord_990714, baseEnd_990714] using wordTrace_append hprefix tailTrace_990714
  have hstable : (prefixWord ++ tailWord_990714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990714).length < 2 ^ (prefixWord ++ tailWord_990714).sum := by decide
  have hdescent : baseEnd_990714 < baseStart_990714 := by decide
  rcases family_descends (prefixWord ++ tailWord_990714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990755 : List Nat := [1, 1, 1, 4, 5, 1, 1, 1, 4, 2, 2]
def baseStart_990755 : Nat := 118140960795 + 990755 * 2 ^ 59
def prefixEnd_990755 : Nat := 4983230072969 + 3 ^ 40 * 990755 * 2
def baseEnd_990755 : Nat := 508733525845376400206107

theorem tailTrace_990755 : CollatzResearch.WordTrace tailWord_990755 prefixEnd_990755 508733525845376400206107 := by
  unfold tailWord_990755
  simp only [CollatzResearch.WordTrace]
  refine ⟨36135803525671317327813719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24090535683780878218542479 36135803525671317327813719)
  ·
    refine ⟨54203705288506975991720579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36135803525671317327813719 54203705288506975991720579)
    ·
      refine ⟨81305557932760463987580869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54203705288506975991720579 81305557932760463987580869)
      ·
        refine ⟨15244792112392586997671413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81305557932760463987580869 15244792112392586997671413)
        ·
          refine ⟨1429199260536805031031695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15244792112392586997671413 1429199260536805031031695)
          ·
            refine ⟨2143798890805207546547543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1429199260536805031031695 2143798890805207546547543)
            ·
              refine ⟨3215698336207811319821315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2143798890805207546547543 3215698336207811319821315)
              ·
                refine ⟨4823547504311716979731973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3215698336207811319821315 4823547504311716979731973)
                ·
                  refine ⟨904415157058446933699745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4823547504311716979731973 904415157058446933699745)
                  ·
                    refine ⟨678311367793835200274809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 904415157058446933699745 678311367793835200274809)
                    ·
                      refine ⟨508733525845376400206107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 678311367793835200274809 508733525845376400206107)
                      ·
                        rfl

theorem cell23_990755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 4, 2, 2].length) (baseStart_990755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990755 prefixEnd_990755 := by exact prefixLift 990755
  have htrace : WordTrace (prefixWord ++ tailWord_990755) baseStart_990755 baseEnd_990755 := by
    simpa [prefixWord, tailWord_990755, baseEnd_990755] using wordTrace_append hprefix tailTrace_990755
  have hstable : (prefixWord ++ tailWord_990755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990755).length < 2 ^ (prefixWord ++ tailWord_990755).sum := by decide
  have hdescent : baseEnd_990755 < baseStart_990755 := by decide
  rcases family_descends (prefixWord ++ tailWord_990755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990771 : List Nat := [1, 1, 1, 2, 4, 3, 2, 1, 2, 3, 3]
def baseStart_990771 : Nat := 118140960795 + 990771 * 2 ^ 59
def prefixEnd_990771 : Nat := 4983230072969 + 3 ^ 40 * 990771 * 2
def baseEnd_990771 : Nat := 508741741535848337606033

theorem tailTrace_990771 : CollatzResearch.WordTrace tailWord_990771 prefixEnd_990771 508741741535848337606033 := by
  unfold tailWord_990771
  simp only [CollatzResearch.WordTrace]
  refine ⟨36136387093613352060396167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24090924729075568040264111 36136387093613352060396167)
  ·
    refine ⟨54204580640420028090594251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36136387093613352060396167 54204580640420028090594251)
    ·
      refine ⟨81306870960630042135891377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54204580640420028090594251 81306870960630042135891377)
      ·
        refine ⟨60980153220472531601918533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81306870960630042135891377 60980153220472531601918533)
        ·
          refine ⟨11433778728838599675359725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60980153220472531601918533 11433778728838599675359725)
          ·
            refine ⟨4287667023314474878259897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11433778728838599675359725 4287667023314474878259897)
            ·
              refine ⟨3215750267485856158694923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4287667023314474878259897 3215750267485856158694923)
              ·
                refine ⟨4823625401228784238042385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3215750267485856158694923 4823625401228784238042385)
                ·
                  refine ⟨3617719050921588178531789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4823625401228784238042385 3617719050921588178531789)
                  ·
                    refine ⟨1356644644095595566949421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3617719050921588178531789 1356644644095595566949421)
                    ·
                      refine ⟨508741741535848337606033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1356644644095595566949421 508741741535848337606033)
                      ·
                        rfl

theorem cell23_990771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 3, 3].length) (baseStart_990771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990771 prefixEnd_990771 := by exact prefixLift 990771
  have htrace : WordTrace (prefixWord ++ tailWord_990771) baseStart_990771 baseEnd_990771 := by
    simpa [prefixWord, tailWord_990771, baseEnd_990771] using wordTrace_append hprefix tailTrace_990771
  have hstable : (prefixWord ++ tailWord_990771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990771).length < 2 ^ (prefixWord ++ tailWord_990771).sum := by decide
  have hdescent : baseEnd_990771 < baseStart_990771 := by decide
  rcases family_descends (prefixWord ++ tailWord_990771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990784 : List Nat := [2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 5]
def baseStart_990784 : Nat := 118140960795 + 990784 * 2 ^ 59
def prefixEnd_990784 : Nat := 4983230072969 + 3 ^ 40 * 990784 * 2
def baseEnd_990784 : Nat := 508748416784356786743473

theorem tailTrace_990784 : CollatzResearch.WordTrace tailWord_990784 prefixEnd_990784 508748416784356786743473 := by
  unfold tailWord_990784
  simp only [CollatzResearch.WordTrace]
  refine ⟨18068430621283127640309703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24091240828377503520412937 18068430621283127640309703)
  ·
    refine ⟨27102645931924691460464555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18068430621283127640309703 27102645931924691460464555)
    ·
      refine ⟨40653968897887037190696833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27102645931924691460464555 40653968897887037190696833)
      ·
        refine ⟨30490476673415277893022625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40653968897887037190696833 30490476673415277893022625)
        ·
          refine ⟨22867857505061458419766969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30490476673415277893022625 22867857505061458419766969)
          ·
            refine ⟨17150893128796093814825227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22867857505061458419766969 17150893128796093814825227)
            ·
              refine ⟨25726339693194140722237841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17150893128796093814825227 25726339693194140722237841)
              ·
                refine ⟨19294754769895605541678381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25726339693194140722237841 19294754769895605541678381)
                ·
                  refine ⟨7235533038710852078129393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19294754769895605541678381 7235533038710852078129393)
                  ·
                    refine ⟨5426649779033139058597045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7235533038710852078129393 5426649779033139058597045)
                    ·
                      refine ⟨508748416784356786743473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5426649779033139058597045 508748416784356786743473)
                      ·
                        rfl

theorem cell23_990784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 5].length) (baseStart_990784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990784 prefixEnd_990784 := by exact prefixLift 990784
  have htrace : WordTrace (prefixWord ++ tailWord_990784) baseStart_990784 baseEnd_990784 := by
    simpa [prefixWord, tailWord_990784, baseEnd_990784] using wordTrace_append hprefix tailTrace_990784
  have hstable : (prefixWord ++ tailWord_990784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990784).length < 2 ^ (prefixWord ++ tailWord_990784).sum := by decide
  have hdescent : baseEnd_990784 < baseStart_990784 := by decide
  rcases family_descends (prefixWord ++ tailWord_990784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990831 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 6, 2, 3]
def baseStart_990831 : Nat := 118140960795 + 990831 * 2 ^ 59
def prefixEnd_990831 : Nat := 4983230072969 + 3 ^ 40 * 990831 * 2
def baseEnd_990831 : Nat := 508772550375118102855757

theorem tailTrace_990831 : CollatzResearch.WordTrace tailWord_990831 prefixEnd_990831 508772550375118102855757 := by
  unfold tailWord_990831
  simp only [CollatzResearch.WordTrace]
  refine ⟨36138575473395982307580347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24092383648930654871720231 36138575473395982307580347)
  ·
    refine ⟨54207863210093973461370521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36138575473395982307580347 54207863210093973461370521)
    ·
      refine ⟨40655897407570480096027891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54207863210093973461370521 40655897407570480096027891)
      ·
        refine ⟨60983846111355720144041837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40655897407570480096027891 60983846111355720144041837)
        ·
          refine ⟨22868942291758395054015689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60983846111355720144041837 22868942291758395054015689)
          ·
            refine ⟨17151706718818796290511767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22868942291758395054015689 17151706718818796290511767)
            ·
              refine ⟨25727560078228194435767651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17151706718818796290511767 25727560078228194435767651)
              ·
                refine ⟨38591340117342291653651477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25727560078228194435767651 38591340117342291653651477)
                ·
                  refine ⟨1808969068000419921264913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 38591340117342291653651477 1808969068000419921264913)
                  ·
                    refine ⟨1356726801000314940948685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1808969068000419921264913 1356726801000314940948685)
                    ·
                      refine ⟨508772550375118102855757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1356726801000314940948685 508772550375118102855757)
                      ·
                        rfl

theorem cell23_990831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 6, 2, 3].length) (baseStart_990831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990831 prefixEnd_990831 := by exact prefixLift 990831
  have htrace : WordTrace (prefixWord ++ tailWord_990831) baseStart_990831 baseEnd_990831 := by
    simpa [prefixWord, tailWord_990831, baseEnd_990831] using wordTrace_append hprefix tailTrace_990831
  have hstable : (prefixWord ++ tailWord_990831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990831).length < 2 ^ (prefixWord ++ tailWord_990831).sum := by decide
  have hdescent : baseEnd_990831 < baseStart_990831 := by decide
  rcases family_descends (prefixWord ++ tailWord_990831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990848 : List Nat := [2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 3]
def baseStart_990848 : Nat := 118140960795 + 990848 * 2 ^ 59
def prefixEnd_990848 : Nat := 4983230072969 + 3 ^ 40 * 990848 * 2
def baseEnd_990848 : Nat := 508781279546244536343179

theorem tailTrace_990848 : CollatzResearch.WordTrace tailWord_990848 prefixEnd_990848 508781279546244536343179 := by
  unfold tailWord_990848
  simp only [CollatzResearch.WordTrace]
  refine ⟨18069597757167197105474599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24092797009556262807299465 18069597757167197105474599)
  ·
    refine ⟨27104396635750795658211899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18069597757167197105474599 27104396635750795658211899)
    ·
      refine ⟨40656594953626193487317849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27104396635750795658211899 40656594953626193487317849)
      ·
        refine ⟨30492446215219645115488387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40656594953626193487317849 30492446215219645115488387)
        ·
          refine ⟨45738669322829467673232581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30492446215219645115488387 45738669322829467673232581)
          ·
            refine ⟨8576000498030525188731109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45738669322829467673232581 8576000498030525188731109)
            ·
              refine ⟨1608000093380723472887083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8576000498030525188731109 1608000093380723472887083)
              ·
                refine ⟨2412000140071085209330625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1608000093380723472887083 2412000140071085209330625)
                ·
                  refine ⟨1809000105053313906997969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2412000140071085209330625 1809000105053313906997969)
                  ·
                    refine ⟨1356750078789985430248477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1809000105053313906997969 1356750078789985430248477)
                    ·
                      refine ⟨508781279546244536343179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1356750078789985430248477 508781279546244536343179)
                      ·
                        rfl

theorem cell23_990848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 3].length) (baseStart_990848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990848 prefixEnd_990848 := by exact prefixLift 990848
  have htrace : WordTrace (prefixWord ++ tailWord_990848) baseStart_990848 baseEnd_990848 := by
    simpa [prefixWord, tailWord_990848, baseEnd_990848] using wordTrace_append hprefix tailTrace_990848
  have hstable : (prefixWord ++ tailWord_990848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990848).length < 2 ^ (prefixWord ++ tailWord_990848).sum := by decide
  have hdescent : baseEnd_990848 < baseStart_990848 := by decide
  rcases family_descends (prefixWord ++ tailWord_990848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990872 : List Nat := [2, 1, 2, 4, 1, 2, 4, 2, 1, 4]
def baseStart_990872 : Nat := 118140960795 + 990872 * 2 ^ 59
def prefixEnd_990872 : Nat := 4983230072969 + 3 ^ 40 * 990872 * 2
def baseEnd_990872 : Nat := 169597867693984147481023

theorem tailTrace_990872 : CollatzResearch.WordTrace tailWord_990872 prefixEnd_990872 169597867693984147481023 := by
  unfold tailWord_990872
  simp only [CollatzResearch.WordTrace]
  refine ⟨18070035433123723154911435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24093380577498297539881913 18070035433123723154911435)
  ·
    refine ⟨27105053149685584732367153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18070035433123723154911435 27105053149685584732367153)
    ·
      refine ⟨20328789862264188549275365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27105053149685584732367153 20328789862264188549275365)
      ·
        refine ⟨3811648099174535352989131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20328789862264188549275365 3811648099174535352989131)
        ·
          refine ⟨5717472148761803029483697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3811648099174535352989131 5717472148761803029483697)
          ·
            refine ⟨4288104111571352272112773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5717472148761803029483697 4288104111571352272112773)
            ·
              refine ⟨804019520919628551021145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4288104111571352272112773 804019520919628551021145)
              ·
                refine ⟨603014640689721413265859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 804019520919628551021145 603014640689721413265859)
                ·
                  refine ⟨904521961034582119898789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 603014640689721413265859 904521961034582119898789)
                  ·
                    refine ⟨169597867693984147481023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 904521961034582119898789 169597867693984147481023)
                    ·
                      rfl

theorem cell23_990872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 2, 1, 4].length) (baseStart_990872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990872 prefixEnd_990872 := by exact prefixLift 990872
  have htrace : WordTrace (prefixWord ++ tailWord_990872) baseStart_990872 baseEnd_990872 := by
    simpa [prefixWord, tailWord_990872, baseEnd_990872] using wordTrace_append hprefix tailTrace_990872
  have hstable : (prefixWord ++ tailWord_990872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990872).length < 2 ^ (prefixWord ++ tailWord_990872).sum := by decide
  have hdescent : baseEnd_990872 < baseStart_990872 := by decide
  rcases family_descends (prefixWord ++ tailWord_990872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990905 : List Nat := [1, 2, 1, 4, 1, 1, 5, 1, 2, 3, 2]
def baseStart_990905 : Nat := 118140960795 + 990905 * 2 ^ 59
def prefixEnd_990905 : Nat := 4983230072969 + 3 ^ 40 * 990905 * 2
def baseEnd_990905 : Nat := 508810547943550813330417

theorem tailTrace_990905 : CollatzResearch.WordTrace tailWord_990905 prefixEnd_990905 508810547943550813330417 := by
  unfold tailWord_990905
  simp only [CollatzResearch.WordTrace]
  refine ⟨36141274475127892945774169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24094182983418595297182779 36141274475127892945774169)
  ·
    refine ⟨27105955856345919709330627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36141274475127892945774169 27105955856345919709330627)
    ·
      refine ⟨40658933784518879563995941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27105955856345919709330627 40658933784518879563995941)
      ·
        refine ⟨7623550084597289918249239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40658933784518879563995941 7623550084597289918249239)
        ·
          refine ⟨11435325126895934877373859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7623550084597289918249239 11435325126895934877373859)
          ·
            refine ⟨17152987690343902316060789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11435325126895934877373859 17152987690343902316060789)
            ·
              refine ⟨1608092595969740842130699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17152987690343902316060789 1608092595969740842130699)
              ·
                refine ⟨2412138893954611263196049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1608092595969740842130699 2412138893954611263196049)
                ·
                  refine ⟨1809104170465958447397037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2412138893954611263196049 1809104170465958447397037)
                  ·
                    refine ⟨678414063924734417773889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1809104170465958447397037 678414063924734417773889)
                    ·
                      refine ⟨508810547943550813330417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 678414063924734417773889 508810547943550813330417)
                      ·
                        rfl

theorem cell23_990905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 2, 3, 2].length) (baseStart_990905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990905 prefixEnd_990905 := by exact prefixLift 990905
  have htrace : WordTrace (prefixWord ++ tailWord_990905) baseStart_990905 baseEnd_990905 := by
    simpa [prefixWord, tailWord_990905, baseEnd_990905] using wordTrace_append hprefix tailTrace_990905
  have hstable : (prefixWord ++ tailWord_990905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990905).length < 2 ^ (prefixWord ++ tailWord_990905).sum := by decide
  have hdescent : baseEnd_990905 < baseStart_990905 := by decide
  rcases family_descends (prefixWord ++ tailWord_990905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990911 : List Nat := [1, 1, 2, 2, 2, 3, 1, 4, 1, 6]
def baseStart_990911 : Nat := 118140960795 + 990911 * 2 ^ 59
def prefixEnd_990911 : Nat := 4983230072969 + 3 ^ 40 * 990911 * 2
def baseEnd_990911 : Nat := 169604542942492596618463

theorem tailTrace_990911 : CollatzResearch.WordTrace tailWord_990911 prefixEnd_990911 169604542942492596618463 := by
  unfold tailWord_990911
  simp only [CollatzResearch.WordTrace]
  refine ⟨36141493313106155970492587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24094328875404103980328391 36141493313106155970492587)
  ·
    refine ⟨54212239969659233955738881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36141493313106155970492587 54212239969659233955738881)
    ·
      refine ⟨40659179977244425466804161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54212239969659233955738881 40659179977244425466804161)
      ·
        refine ⟨30494384982933319100103121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40659179977244425466804161 30494384982933319100103121)
        ·
          refine ⟨22870788737199989325077341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30494384982933319100103121 22870788737199989325077341)
          ·
            refine ⟨8576545776449995996904003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22870788737199989325077341 8576545776449995996904003)
            ·
              refine ⟨12864818664674993995356005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8576545776449995996904003 12864818664674993995356005)
              ·
                refine ⟨2412153499626561374129251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12864818664674993995356005 2412153499626561374129251)
                ·
                  refine ⟨3618230249439842061193877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2412153499626561374129251 3618230249439842061193877)
                  ·
                    refine ⟨169604542942492596618463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3618230249439842061193877 169604542942492596618463)
                    ·
                      rfl

theorem cell23_990911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 6].length) (baseStart_990911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990911 prefixEnd_990911 := by exact prefixLift 990911
  have htrace : WordTrace (prefixWord ++ tailWord_990911) baseStart_990911 baseEnd_990911 := by
    simpa [prefixWord, tailWord_990911, baseEnd_990911] using wordTrace_append hprefix tailTrace_990911
  have hstable : (prefixWord ++ tailWord_990911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990911).length < 2 ^ (prefixWord ++ tailWord_990911).sum := by decide
  have hdescent : baseEnd_990911 < baseStart_990911 := by decide
  rcases family_descends (prefixWord ++ tailWord_990911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990912 : List Nat := [2, 1, 1, 2, 4, 1, 4, 3, 1, 1, 3]
def baseStart_990912 : Nat := 118140960795 + 990912 * 2 ^ 59
def prefixEnd_990912 : Nat := 4983230072969 + 3 ^ 40 * 990912 * 2
def baseEnd_990912 : Nat := 508814142308132285942885

theorem tailTrace_990912 : CollatzResearch.WordTrace tailWord_990912 prefixEnd_990912 508814142308132285942885 := by
  unfold tailWord_990912
  simp only [CollatzResearch.WordTrace]
  refine ⟨18070764893051266570639495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24094353190735022094185993 18070764893051266570639495)
  ·
    refine ⟨27106147339576899855959243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18070764893051266570639495 27106147339576899855959243)
    ·
      refine ⟨40659221009365349783938865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27106147339576899855959243 40659221009365349783938865)
      ·
        refine ⟨30494415757024012337954149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40659221009365349783938865 30494415757024012337954149)
        ·
          refine ⟨5717702954442002313366403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30494415757024012337954149 5717702954442002313366403)
          ·
            refine ⟨8576554431663003470049605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5717702954442002313366403 8576554431663003470049605)
            ·
              refine ⟨1608103955936813150634301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8576554431663003470049605 1608103955936813150634301)
              ·
                refine ⟨603038983476304931487863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1608103955936813150634301 603038983476304931487863)
                ·
                  refine ⟨904558475214457397231795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 603038983476304931487863 904558475214457397231795)
                  ·
                    refine ⟨1356837712821686095847693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 904558475214457397231795 1356837712821686095847693)
                    ·
                      refine ⟨508814142308132285942885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1356837712821686095847693 508814142308132285942885)
                      ·
                        rfl

theorem cell23_990912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 3, 1, 1, 3].length) (baseStart_990912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990912 prefixEnd_990912 := by exact prefixLift 990912
  have htrace : WordTrace (prefixWord ++ tailWord_990912) baseStart_990912 baseEnd_990912 := by
    simpa [prefixWord, tailWord_990912, baseEnd_990912] using wordTrace_append hprefix tailTrace_990912
  have hstable : (prefixWord ++ tailWord_990912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990912).length < 2 ^ (prefixWord ++ tailWord_990912).sum := by decide
  have hdescent : baseEnd_990912 < baseStart_990912 := by decide
  rcases family_descends (prefixWord ++ tailWord_990912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990928 : List Nat := [2, 1, 1, 1, 1, 2, 1, 8, 2, 4]
def baseStart_990928 : Nat := 118140960795 + 990928 * 2 ^ 59
def prefixEnd_990928 : Nat := 4983230072969 + 3 ^ 40 * 990928 * 2
def baseEnd_990928 : Nat := 169607452666201407780937

theorem tailTrace_990928 : CollatzResearch.WordTrace tailWord_990928 prefixEnd_990928 169607452666201407780937 := by
  unfold tailWord_990928
  simp only [CollatzResearch.WordTrace]
  refine ⟨18071056677022283936930719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24094742236029711915907625 18071056677022283936930719)
  ·
    refine ⟨27106585015533425905396079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18071056677022283936930719 27106585015533425905396079)
    ·
      refine ⟨40659877523300138858094119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27106585015533425905396079 40659877523300138858094119)
      ·
        refine ⟨60989816284950208287141179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40659877523300138858094119 60989816284950208287141179)
        ·
          refine ⟨91484724427425312430711769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60989816284950208287141179 91484724427425312430711769)
          ·
            refine ⟨68613543320568984323033827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91484724427425312430711769 68613543320568984323033827)
            ·
              refine ⟨102920314980853476484550741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68613543320568984323033827 102920314980853476484550741)
              ·
                refine ⟨1206097441181876677553329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 102920314980853476484550741 1206097441181876677553329)
                ·
                  refine ⟨904573080886407508164997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1206097441181876677553329 904573080886407508164997)
                  ·
                    refine ⟨169607452666201407780937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 904573080886407508164997 169607452666201407780937)
                    ·
                      rfl

theorem cell23_990928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 8, 2, 4].length) (baseStart_990928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990928 prefixEnd_990928 := by exact prefixLift 990928
  have htrace : WordTrace (prefixWord ++ tailWord_990928) baseStart_990928 baseEnd_990928 := by
    simpa [prefixWord, tailWord_990928, baseEnd_990928] using wordTrace_append hprefix tailTrace_990928
  have hstable : (prefixWord ++ tailWord_990928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990928).length < 2 ^ (prefixWord ++ tailWord_990928).sum := by decide
  have hdescent : baseEnd_990928 < baseStart_990928 := by decide
  rcases family_descends (prefixWord ++ tailWord_990928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990938 : List Nat := [3, 1, 1, 2, 2, 4, 1, 2, 1, 1, 5]
def baseStart_990938 : Nat := 118140960795 + 990938 * 2 ^ 59
def prefixEnd_990938 : Nat := 4983230072969 + 3 ^ 40 * 990938 * 2
def baseEnd_990938 : Nat := 508827492805149184217765

theorem tailTrace_990938 : CollatzResearch.WordTrace tailWord_990938 prefixEnd_990938 508827492805149184217765 := by
  unfold tailWord_990938
  simp only [CollatzResearch.WordTrace]
  refine ⟨9035619521002084895431367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24094985389338893054483645 9035619521002084895431367)
  ·
    refine ⟨13553429281503127343147051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9035619521002084895431367 13553429281503127343147051)
    ·
      refine ⟨20330143922254691014720577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13553429281503127343147051 20330143922254691014720577)
      ·
        refine ⟨15247607941691018261040433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20330143922254691014720577 15247607941691018261040433)
        ·
          refine ⟨11435705956268263695780325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15247607941691018261040433 11435705956268263695780325)
          ·
            refine ⟨2144194866800299442958811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11435705956268263695780325 2144194866800299442958811)
            ·
              refine ⟨3216292300200449164438217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2144194866800299442958811 3216292300200449164438217)
              ·
                refine ⟨2412219225150336873328663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3216292300200449164438217 2412219225150336873328663)
                ·
                  refine ⟨3618328837725505309992995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2412219225150336873328663 3618328837725505309992995)
                  ·
                    refine ⟨5427493256588257964989493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3618328837725505309992995 5427493256588257964989493)
                    ·
                      refine ⟨508827492805149184217765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5427493256588257964989493 508827492805149184217765)
                      ·
                        rfl

theorem cell23_990938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_990938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990938 prefixEnd_990938 := by exact prefixLift 990938
  have htrace : WordTrace (prefixWord ++ tailWord_990938) baseStart_990938 baseEnd_990938 := by
    simpa [prefixWord, tailWord_990938, baseEnd_990938] using wordTrace_append hprefix tailTrace_990938
  have hstable : (prefixWord ++ tailWord_990938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990938).length < 2 ^ (prefixWord ++ tailWord_990938).sum := by decide
  have hdescent : baseEnd_990938 < baseStart_990938 := by decide
  rcases family_descends (prefixWord ++ tailWord_990938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990945 : List Nat := [1, 2, 3, 1, 5, 2, 1, 1, 1, 6]
def baseStart_990945 : Nat := 118140960795 + 990945 * 2 ^ 59
def prefixEnd_990945 : Nat := 4983230072969 + 3 ^ 40 * 990945 * 2
def baseEnd_990945 : Nat := 169610362389910218943411

theorem tailTrace_990945 : CollatzResearch.WordTrace tailWord_990945 prefixEnd_990945 169610362389910218943411 := by
  unfold tailWord_990945
  simp only [CollatzResearch.WordTrace]
  refine ⟨36142733394982979777230289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24095155596655319851486859 36142733394982979777230289)
  ·
    refine ⟨27107050046237234832922717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36142733394982979777230289 27107050046237234832922717)
    ·
      refine ⟨10165143767338963062346019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27107050046237234832922717 10165143767338963062346019)
      ·
        refine ⟨15247715651008444593519029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10165143767338963062346019 15247715651008444593519029)
        ·
          refine ⟨1429473342282041680642409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15247715651008444593519029 1429473342282041680642409)
          ·
            refine ⟨1072105006711531260481807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1429473342282041680642409 1072105006711531260481807)
            ·
              refine ⟨1608157510067296890722711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1072105006711531260481807 1608157510067296890722711)
              ·
                refine ⟨2412236265100945336084067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1608157510067296890722711 2412236265100945336084067)
                ·
                  refine ⟨3618354397651418004126101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2412236265100945336084067 3618354397651418004126101)
                  ·
                    refine ⟨169610362389910218943411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3618354397651418004126101 169610362389910218943411)
                    ·
                      rfl

theorem cell23_990945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 6].length) (baseStart_990945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990945 prefixEnd_990945 := by exact prefixLift 990945
  have htrace : WordTrace (prefixWord ++ tailWord_990945) baseStart_990945 baseEnd_990945 := by
    simpa [prefixWord, tailWord_990945, baseEnd_990945] using wordTrace_append hprefix tailTrace_990945
  have hstable : (prefixWord ++ tailWord_990945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990945).length < 2 ^ (prefixWord ++ tailWord_990945).sum := by decide
  have hdescent : baseEnd_990945 < baseStart_990945 := by decide
  rcases family_descends (prefixWord ++ tailWord_990945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990952 : List Nat := [2, 1, 4, 1, 3, 1, 2, 2, 3, 2, 2]
def baseStart_990952 : Nat := 118140960795 + 990952 * 2 ^ 59
def prefixEnd_990952 : Nat := 4983230072969 + 3 ^ 40 * 990952 * 2
def baseEnd_990952 : Nat := 508834681534312129442701

theorem tailTrace_990952 : CollatzResearch.WordTrace tailWord_990952 prefixEnd_990952 508834681534312129442701 := by
  unfold tailWord_990952
  simp only [CollatzResearch.WordTrace]
  refine ⟨18071494352978809986367555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24095325803971746648490073 18071494352978809986367555)
  ·
    refine ⟨27107241529468214979551333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18071494352978809986367555 27107241529468214979551333)
    ·
      refine ⟨5082607786775290308665875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27107241529468214979551333 5082607786775290308665875)
      ·
        refine ⟨7623911680162935462998813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5082607786775290308665875 7623911680162935462998813)
        ·
          refine ⟨2858966880061100798624555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7623911680162935462998813 2858966880061100798624555)
          ·
            refine ⟨4288450320091651197936833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2858966880061100798624555 4288450320091651197936833)
            ·
              refine ⟨3216337740068738398452625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4288450320091651197936833 3216337740068738398452625)
              ·
                refine ⟨2412253305051553798839469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3216337740068738398452625 2412253305051553798839469)
                ·
                  refine ⟨904594989394332674564801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2412253305051553798839469 904594989394332674564801)
                  ·
                    refine ⟨678446242045749505923601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 904594989394332674564801 678446242045749505923601)
                    ·
                      refine ⟨508834681534312129442701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 678446242045749505923601 508834681534312129442701)
                      ·
                        rfl

theorem cell23_990952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 3, 2, 2].length) (baseStart_990952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990952 prefixEnd_990952 := by exact prefixLift 990952
  have htrace : WordTrace (prefixWord ++ tailWord_990952) baseStart_990952 baseEnd_990952 := by
    simpa [prefixWord, tailWord_990952, baseEnd_990952] using wordTrace_append hprefix tailTrace_990952
  have hstable : (prefixWord ++ tailWord_990952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990952).length < 2 ^ (prefixWord ++ tailWord_990952).sum := by decide
  have hdescent : baseEnd_990952 < baseStart_990952 := by decide
  rcases family_descends (prefixWord ++ tailWord_990952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990985 : List Nat := [1, 2, 1, 1, 3, 2, 1, 6, 2, 1, 3]
def baseStart_990985 : Nat := 118140960795 + 990985 * 2 ^ 59
def prefixEnd_990985 : Nat := 4983230072969 + 3 ^ 40 * 990985 * 2
def baseEnd_990985 : Nat := 508851626395910500330049

theorem tailTrace_990985 : CollatzResearch.WordTrace tailWord_990985 prefixEnd_990985 508851626395910500330049 := by
  unfold tailWord_990985
  simp only [CollatzResearch.WordTrace]
  refine ⟨36144192314838066608686409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24096128209892044405790939 36144192314838066608686409)
  ·
    refine ⟨27108144236128549956514807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36144192314838066608686409 27108144236128549956514807)
    ·
      refine ⟨40662216354192824934772211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27108144236128549956514807 40662216354192824934772211)
      ·
        refine ⟨60993324531289237402158317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40662216354192824934772211 60993324531289237402158317)
        ·
          refine ⟨22872496699233464025809369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60993324531289237402158317 22872496699233464025809369)
          ·
            refine ⟨17154372524425098019357027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22872496699233464025809369 17154372524425098019357027)
            ·
              refine ⟨25731558786637647029035541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17154372524425098019357027 25731558786637647029035541)
              ·
                refine ⟨1206166818123639704486041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25731558786637647029035541 1206166818123639704486041)
                ·
                  refine ⟨904625113592729778364531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1206166818123639704486041 904625113592729778364531)
                  ·
                    refine ⟨1356937670389094667546797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 904625113592729778364531 1356937670389094667546797)
                    ·
                      refine ⟨508851626395910500330049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1356937670389094667546797 508851626395910500330049)
                      ·
                        rfl

theorem cell23_990985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 6, 2, 1, 3].length) (baseStart_990985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990985 prefixEnd_990985 := by exact prefixLift 990985
  have htrace : WordTrace (prefixWord ++ tailWord_990985) baseStart_990985 baseEnd_990985 := by
    simpa [prefixWord, tailWord_990985, baseEnd_990985] using wordTrace_append hprefix tailTrace_990985
  have hstable : (prefixWord ++ tailWord_990985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990985).length < 2 ^ (prefixWord ++ tailWord_990985).sum := by decide
  have hdescent : baseEnd_990985 < baseStart_990985 := by decide
  rcases family_descends (prefixWord ++ tailWord_990985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990986 : List Nat := [3, 1, 2, 2, 1, 4, 3, 2, 1, 2, 2]
def baseStart_990986 : Nat := 118140960795 + 990986 * 2 ^ 59
def prefixEnd_990986 : Nat := 4983230072969 + 3 ^ 40 * 990986 * 2
def baseEnd_990986 : Nat := 508852139876564996417545

theorem tailTrace_990986 : CollatzResearch.WordTrace tailWord_990986 prefixEnd_990986 508852139876564996417545 := by
  unfold tailWord_990986
  simp only [CollatzResearch.WordTrace]
  refine ⟨9036057196958610944868203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24096152525222962519648541 9036057196958610944868203)
  ·
    refine ⟨13554085795437916417302305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9036057196958610944868203 13554085795437916417302305)
    ·
      refine ⟨10165564346578437312976729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13554085795437916417302305 10165564346578437312976729)
      ·
        refine ⟨7624173259933827984732547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10165564346578437312976729 7624173259933827984732547)
        ·
          refine ⟨11436259889900741977098821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7624173259933827984732547 11436259889900741977098821)
          ·
            refine ⟨2144298729356389120706029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11436259889900741977098821 2144298729356389120706029)
            ·
              refine ⟨804112023508645920264761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2144298729356389120706029 804112023508645920264761)
              ·
                refine ⟨603084017631484440198571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 804112023508645920264761 603084017631484440198571)
                ·
                  refine ⟨904626026447226660297857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 603084017631484440198571 904626026447226660297857)
                  ·
                    refine ⟨678469519835419995223393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 904626026447226660297857 678469519835419995223393)
                    ·
                      refine ⟨508852139876564996417545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 678469519835419995223393 508852139876564996417545)
                      ·
                        rfl

theorem cell23_990986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 2, 1, 2, 2].length) (baseStart_990986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990986 prefixEnd_990986 := by exact prefixLift 990986
  have htrace : WordTrace (prefixWord ++ tailWord_990986) baseStart_990986 baseEnd_990986 := by
    simpa [prefixWord, tailWord_990986, baseEnd_990986] using wordTrace_append hprefix tailTrace_990986
  have hstable : (prefixWord ++ tailWord_990986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990986).length < 2 ^ (prefixWord ++ tailWord_990986).sum := by decide
  have hdescent : baseEnd_990986 < baseStart_990986 := by decide
  rcases family_descends (prefixWord ++ tailWord_990986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990996 : List Nat := [2, 4, 4, 1, 1, 1, 1, 3, 2, 4]
def baseStart_990996 : Nat := 118140960795 + 990996 * 2 ^ 59
def prefixEnd_990996 : Nat := 4983230072969 + 3 ^ 40 * 990996 * 2
def baseEnd_990996 : Nat := 169619091561036652430833

theorem tailTrace_990996 : CollatzResearch.WordTrace tailWord_990996 prefixEnd_990996 169619091561036652430833 := by
  unfold tailWord_990996
  simp only [CollatzResearch.WordTrace]
  refine ⟨18072296758899107743668421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24096395678532143658224561 18072296758899107743668421)
  ·
    refine ⟨3388555642293582701937829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18072296758899107743668421 3388555642293582701937829)
    ·
      refine ⟨635354182930046756613343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3388555642293582701937829 635354182930046756613343)
      ·
        refine ⟨953031274395070134920015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 635354182930046756613343 953031274395070134920015)
        ·
          refine ⟨1429546911592605202380023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 953031274395070134920015 1429546911592605202380023)
          ·
            refine ⟨2144320367388907803570035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1429546911592605202380023 2144320367388907803570035)
            ·
              refine ⟨3216480551083361705355053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2144320367388907803570035 3216480551083361705355053)
              ·
                refine ⟨1206180206656260639508145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3216480551083361705355053 1206180206656260639508145)
                ·
                  refine ⟨904635154992195479631109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1206180206656260639508145 904635154992195479631109)
                  ·
                    refine ⟨169619091561036652430833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 904635154992195479631109 169619091561036652430833)
                    ·
                      rfl

theorem cell23_990996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_990996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_990996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_990996 prefixEnd_990996 := by exact prefixLift 990996
  have htrace : WordTrace (prefixWord ++ tailWord_990996) baseStart_990996 baseEnd_990996 := by
    simpa [prefixWord, tailWord_990996, baseEnd_990996] using wordTrace_append hprefix tailTrace_990996
  have hstable : (prefixWord ++ tailWord_990996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990996).length < 2 ^ (prefixWord ++ tailWord_990996).sum := by decide
  have hdescent : baseEnd_990996 < baseStart_990996 := by decide
  rcases family_descends (prefixWord ++ tailWord_990996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991001 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 6, 6]
def baseStart_991001 : Nat := 118140960795 + 991001 * 2 ^ 59
def prefixEnd_991001 : Nat := 4983230072969 + 3 ^ 40 * 991001 * 2
def baseEnd_991001 : Nat := 169619947362127479243325

theorem tailTrace_991001 : CollatzResearch.WordTrace tailWord_991001 prefixEnd_991001 169619947362127479243325 := by
  unfold tailWord_991001
  simp only [CollatzResearch.WordTrace]
  refine ⟨36144775882780101341268857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24096517255186734227512571 36144775882780101341268857)
  ·
    refine ⟨27108581912085076005951643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36144775882780101341268857 27108581912085076005951643)
    ·
      refine ⟨40662872868127614008927465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27108581912085076005951643 40662872868127614008927465)
      ·
        refine ⟨30497154651095710506695599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40662872868127614008927465 30497154651095710506695599)
        ·
          refine ⟨45745731976643565760043399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30497154651095710506695599 45745731976643565760043399)
          ·
            refine ⟨68618597964965348640065099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45745731976643565760043399 68618597964965348640065099)
            ·
              refine ⟨102927896947448022960097649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68618597964965348640065099 102927896947448022960097649)
              ·
                refine ⟨77195922710586017220073237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102927896947448022960097649 77195922710586017220073237)
                ·
                  refine ⟨3618558877058719557190933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 77195922710586017220073237 3618558877058719557190933)
                  ·
                    refine ⟨169619947362127479243325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3618558877058719557190933 169619947362127479243325)
                    ·
                      rfl

theorem cell23_991001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 6].length) (baseStart_991001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_991001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_991001 prefixEnd_991001 := by exact prefixLift 991001
  have htrace : WordTrace (prefixWord ++ tailWord_991001) baseStart_991001 baseEnd_991001 := by
    simpa [prefixWord, tailWord_991001, baseEnd_991001] using wordTrace_append hprefix tailTrace_991001
  have hstable : (prefixWord ++ tailWord_991001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991001).length < 2 ^ (prefixWord ++ tailWord_991001).sum := by decide
  have hdescent : baseEnd_991001 < baseStart_991001 := by decide
  rcases family_descends (prefixWord ++ tailWord_991001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991002 : List Nat := [3, 1, 1, 3, 2, 3, 1, 3, 2, 1, 3]
def baseStart_991002 : Nat := 118140960795 + 991002 * 2 ^ 59
def prefixEnd_991002 : Nat := 4983230072969 + 3 ^ 40 * 991002 * 2
def baseEnd_991002 : Nat := 508860355567036933817471

theorem tailTrace_991002 : CollatzResearch.WordTrace tailWord_991002 prefixEnd_991002 508860355567036933817471 := by
  unfold tailWord_991002
  simp only [CollatzResearch.WordTrace]
  refine ⟨9036203088944119628013815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24096541570517652341370173 9036203088944119628013815)
  ·
    refine ⟨13554304633416179442020723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9036203088944119628013815 13554304633416179442020723)
    ·
      refine ⟨20331456950124269163031085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13554304633416179442020723 20331456950124269163031085)
      ·
        refine ⟨7624296356296600936136657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20331456950124269163031085 7624296356296600936136657)
        ·
          refine ⟨5718222267222450702102493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7624296356296600936136657 5718222267222450702102493)
          ·
            refine ⟨2144333350208419013288435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5718222267222450702102493 2144333350208419013288435)
            ·
              refine ⟨3216500025312628519932653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2144333350208419013288435 3216500025312628519932653)
              ·
                refine ⟨1206187509492235694974745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3216500025312628519932653 1206187509492235694974745)
                ·
                  refine ⟨904640632119176771231059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1206187509492235694974745 904640632119176771231059)
                  ·
                    refine ⟨1356960948178765156846589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 904640632119176771231059 1356960948178765156846589)
                    ·
                      refine ⟨508860355567036933817471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1356960948178765156846589 508860355567036933817471)
                      ·
                        rfl

theorem cell23_991002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_991002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_991002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_991002 prefixEnd_991002 := by exact prefixLift 991002
  have htrace : WordTrace (prefixWord ++ tailWord_991002) baseStart_991002 baseEnd_991002 := by
    simpa [prefixWord, tailWord_991002, baseEnd_991002] using wordTrace_append hprefix tailTrace_991002
  have hstable : (prefixWord ++ tailWord_991002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991002).length < 2 ^ (prefixWord ++ tailWord_991002).sum := by decide
  have hdescent : baseEnd_991002 < baseStart_991002 := by decide
  rcases family_descends (prefixWord ++ tailWord_991002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991012 : List Nat := [2, 3, 1, 3, 2, 2, 1, 1, 3, 3, 2]
def baseStart_991012 : Nat := 118140960795 + 991012 * 2 ^ 59
def prefixEnd_991012 : Nat := 4983230072969 + 3 ^ 40 * 991012 * 2
def baseEnd_991012 : Nat := 508865490373581894692425

theorem tailTrace_991012 : CollatzResearch.WordTrace tailWord_991012 prefixEnd_991012 508865490373581894692425 := by
  unfold tailWord_991012
  simp only [CollatzResearch.WordTrace]
  refine ⟨18072588542870125109959645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24096784723826833479946193 18072588542870125109959645)
  ·
    refine ⟨6777220703576296916234867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18072588542870125109959645 6777220703576296916234867)
    ·
      refine ⟨10165831055364445374352301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6777220703576296916234867 10165831055364445374352301)
      ·
        refine ⟨3812186645761667015382113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10165831055364445374352301 3812186645761667015382113)
        ·
          refine ⟨2859139984321250261536585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3812186645761667015382113 2859139984321250261536585)
          ·
            refine ⟨2144354988240937696152439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2859139984321250261536585 2144354988240937696152439)
            ·
              refine ⟨3216532482361406544228659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2144354988240937696152439 3216532482361406544228659)
              ·
                refine ⟨4824798723542109816342989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3216532482361406544228659 4824798723542109816342989)
                ·
                  refine ⟨1809299521328291181128621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4824798723542109816342989 1809299521328291181128621)
                  ·
                    refine ⟨678487320498109192923233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1809299521328291181128621 678487320498109192923233)
                    ·
                      refine ⟨508865490373581894692425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 678487320498109192923233 508865490373581894692425)
                      ·
                        rfl

theorem cell23_991012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_991012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_991012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_991012 prefixEnd_991012 := by exact prefixLift 991012
  have htrace : WordTrace (prefixWord ++ tailWord_991012) baseStart_991012 baseEnd_991012 := by
    simpa [prefixWord, tailWord_991012, baseEnd_991012] using wordTrace_append hprefix tailTrace_991012
  have hstable : (prefixWord ++ tailWord_991012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991012).length < 2 ^ (prefixWord ++ tailWord_991012).sum := by decide
  have hdescent : baseEnd_991012 < baseStart_991012 := by decide
  rcases family_descends (prefixWord ++ tailWord_991012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991025 : List Nat := [1, 2, 2, 3, 2, 2, 1, 1, 3, 4, 2]
def baseStart_991025 : Nat := 118140960795 + 991025 * 2 ^ 59
def prefixEnd_991025 : Nat := 4983230072969 + 3 ^ 40 * 991025 * 2
def baseEnd_991025 : Nat := 508872165622090343829865

theorem tailTrace_991025 : CollatzResearch.WordTrace tailWord_991025 prefixEnd_991025 508872165622090343829865 := by
  unfold tailWord_991025
  simp only [CollatzResearch.WordTrace]
  refine ⟨36145651234693153440142529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24097100823128768960095019 36145651234693153440142529)
  ·
    refine ⟨27109238426019865080106897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36145651234693153440142529 27109238426019865080106897)
    ·
      refine ⟨20331928819514898810080173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27109238426019865080106897 20331928819514898810080173)
      ·
        refine ⟨7624473307318087053780065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20331928819514898810080173 7624473307318087053780065)
        ·
          refine ⟨5718354980488565290335049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7624473307318087053780065 5718354980488565290335049)
          ·
            refine ⟨4288766235366423967751287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5718354980488565290335049 4288766235366423967751287)
            ·
              refine ⟨6433149353049635951626931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4288766235366423967751287 6433149353049635951626931)
              ·
                refine ⟨9649724029574453927440397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6433149353049635951626931 9649724029574453927440397)
                ·
                  refine ⟨3618646511090420222790149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9649724029574453927440397 3618646511090420222790149)
                  ·
                    refine ⟨678496220829453791773153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3618646511090420222790149 678496220829453791773153)
                    ·
                      refine ⟨508872165622090343829865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 678496220829453791773153 508872165622090343829865)
                      ·
                        rfl

theorem cell23_991025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 4, 2].length) (baseStart_991025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_991025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_991025 prefixEnd_991025 := by exact prefixLift 991025
  have htrace : WordTrace (prefixWord ++ tailWord_991025) baseStart_991025 baseEnd_991025 := by
    simpa [prefixWord, tailWord_991025, baseEnd_991025] using wordTrace_append hprefix tailTrace_991025
  have hstable : (prefixWord ++ tailWord_991025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991025).length < 2 ^ (prefixWord ++ tailWord_991025).sum := by decide
  have hdescent : baseEnd_991025 < baseStart_991025 := by decide
  rcases family_descends (prefixWord ++ tailWord_991025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991031 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 11]
def baseStart_991031 : Nat := 118140960795 + 991031 * 2 ^ 59
def prefixEnd_991031 : Nat := 4983230072969 + 3 ^ 40 * 991031 * 2
def baseEnd_991031 : Nat := 56541694056224146706093

theorem tailTrace_991031 : CollatzResearch.WordTrace tailWord_991031 prefixEnd_991031 56541694056224146706093 := by
  unfold tailWord_991031
  simp only [CollatzResearch.WordTrace]
  refine ⟨36145870072671416464860947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24097246715114277643240631 36145870072671416464860947)
  ·
    refine ⟨54218805109007124697291421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36145870072671416464860947 54218805109007124697291421)
    ·
      refine ⟨20332051915877671761484283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54218805109007124697291421 20332051915877671761484283)
      ·
        refine ⟨30498077873816507642226425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20332051915877671761484283 30498077873816507642226425)
        ·
          refine ⟨22873558405362380731669819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30498077873816507642226425 22873558405362380731669819)
          ·
            refine ⟨34310337608043571097504729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22873558405362380731669819 34310337608043571097504729)
            ·
              refine ⟨25732753206032678323128547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34310337608043571097504729 25732753206032678323128547)
              ·
                refine ⟨38599129809049017484692821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25732753206032678323128547 38599129809049017484692821)
                ·
                  refine ⟨56541694056224146706093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 38599129809049017484692821 56541694056224146706093)
                  ·
                    rfl

theorem cell23_991031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 11].length) (baseStart_991031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_991031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_991031 prefixEnd_991031 := by exact prefixLift 991031
  have htrace : WordTrace (prefixWord ++ tailWord_991031) baseStart_991031 baseEnd_991031 := by
    simpa [prefixWord, tailWord_991031, baseEnd_991031] using wordTrace_append hprefix tailTrace_991031
  have hstable : (prefixWord ++ tailWord_991031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991031).length < 2 ^ (prefixWord ++ tailWord_991031).sum := by decide
  have hdescent : baseEnd_991031 < baseStart_991031 := by decide
  rcases family_descends (prefixWord ++ tailWord_991031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991125 : List Nat := [1, 3, 2, 1, 1, 3, 1, 4, 3, 4]
def baseStart_991125 : Nat := 118140960795 + 991125 * 2 ^ 59
def prefixEnd_991125 : Nat := 4983230072969 + 3 ^ 40 * 991125 * 2
def baseEnd_991125 : Nat := 169641171229179984193135

theorem tailTrace_991125 : CollatzResearch.WordTrace tailWord_991125 prefixEnd_991125 169641171229179984193135 := by
  unfold tailWord_991125
  simp only [CollatzResearch.WordTrace]
  refine ⟨36149298534330870518782829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24099532356220580345855219 36149298534330870518782829)
  ·
    refine ⟨13555986950374076444543561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36149298534330870518782829 13555986950374076444543561)
    ·
      refine ⟨10166990212780557333407671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13555986950374076444543561 10166990212780557333407671)
      ·
        refine ⟨15250485319170836000111507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10166990212780557333407671 15250485319170836000111507)
        ·
          refine ⟨22875727978756254000167261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15250485319170836000111507 22875727978756254000167261)
          ·
            refine ⟨8578397992033595250062723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22875727978756254000167261 8578397992033595250062723)
            ·
              refine ⟨12867596988050392875094085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8578397992033595250062723 12867596988050392875094085)
              ·
                refine ⟨2412674435259448664080141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12867596988050392875094085 2412674435259448664080141)
                ·
                  refine ⟨904752913222293249030053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2412674435259448664080141 904752913222293249030053)
                  ·
                    refine ⟨169641171229179984193135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 904752913222293249030053 169641171229179984193135)
                    ·
                      rfl

theorem cell23_991125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 3, 4].length) (baseStart_991125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_991125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_991125 prefixEnd_991125 := by exact prefixLift 991125
  have htrace : WordTrace (prefixWord ++ tailWord_991125) baseStart_991125 baseEnd_991125 := by
    simpa [prefixWord, tailWord_991125, baseEnd_991125] using wordTrace_append hprefix tailTrace_991125
  have hstable : (prefixWord ++ tailWord_991125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991125).length < 2 ^ (prefixWord ++ tailWord_991125).sum := by decide
  have hdescent : baseEnd_991125 < baseStart_991125 := by decide
  rcases family_descends (prefixWord ++ tailWord_991125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991182 : List Nat := [4, 1, 1, 1, 2, 2, 2, 1, 5, 1, 3]
def baseStart_991182 : Nat := 118140960795 + 991182 * 2 ^ 59
def prefixEnd_991182 : Nat := 4983230072969 + 3 ^ 40 * 991182 * 2
def baseEnd_991182 : Nat := 508952782084846229566643

theorem tailTrace_991182 : CollatzResearch.WordTrace tailWord_991182 prefixEnd_991182 508952782084846229566643 := by
  unfold tailWord_991182
  simp only [CollatzResearch.WordTrace]
  refine ⟨4518922186890546156700975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24100918330082912835738533 4518922186890546156700975)
  ·
    refine ⟨6778383280335819235051463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4518922186890546156700975 6778383280335819235051463)
    ·
      refine ⟨10167574920503728852577195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6778383280335819235051463 10167574920503728852577195)
      ·
        refine ⟨15251362380755593278865793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10167574920503728852577195 15251362380755593278865793)
        ·
          refine ⟨11438521785566694959149345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15251362380755593278865793 11438521785566694959149345)
          ·
            refine ⟨8578891339175021219362009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11438521785566694959149345 8578891339175021219362009)
            ·
              refine ⟨6434168504381265914521507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8578891339175021219362009 6434168504381265914521507)
              ·
                refine ⟨9651252756571898871782261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6434168504381265914521507 9651252756571898871782261)
                ·
                  refine ⟨904804945928615519229587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9651252756571898871782261 904804945928615519229587)
                  ·
                    refine ⟨1357207418892923278844381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 904804945928615519229587 1357207418892923278844381)
                    ·
                      refine ⟨508952782084846229566643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1357207418892923278844381 508952782084846229566643)
                      ·
                        rfl

theorem cell23_991182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 5, 1, 3].length) (baseStart_991182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_991182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_991182 prefixEnd_991182 := by exact prefixLift 991182
  have htrace : WordTrace (prefixWord ++ tailWord_991182) baseStart_991182 baseEnd_991182 := by
    simpa [prefixWord, tailWord_991182, baseEnd_991182] using wordTrace_append hprefix tailTrace_991182
  have hstable : (prefixWord ++ tailWord_991182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991182).length < 2 ^ (prefixWord ++ tailWord_991182).sum := by decide
  have hdescent : baseEnd_991182 < baseStart_991182 := by decide
  rcases family_descends (prefixWord ++ tailWord_991182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991185 : List Nat := [1, 2, 2, 1, 2, 1, 2, 6, 1, 5]
def baseStart_991185 : Nat := 118140960795 + 991185 * 2 ^ 59
def prefixEnd_991185 : Nat := 4983230072969 + 3 ^ 40 * 991185 * 2
def baseEnd_991185 : Nat := 169651440842269905943043

theorem tailTrace_991185 : CollatzResearch.WordTrace tailWord_991185 prefixEnd_991185 169651440842269905943043 := by
  unfold tailWord_991185
  simp only [CollatzResearch.WordTrace]
  refine ⟨36151486914113500765967009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24100991276075667177311339 36151486914113500765967009)
  ·
    refine ⟨27113615185585125574475257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36151486914113500765967009 27113615185585125574475257)
    ·
      refine ⟨20335211389188844180856443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27113615185585125574475257 20335211389188844180856443)
      ·
        refine ⟨30502817083783266271284665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20335211389188844180856443 30502817083783266271284665)
        ·
          refine ⟨22877112812837449703463499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30502817083783266271284665 22877112812837449703463499)
          ·
            refine ⟨34315669219256174555195249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22877112812837449703463499 34315669219256174555195249)
            ·
              refine ⟨25736751914442130916396437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34315669219256174555195249 25736751914442130916396437)
              ·
                refine ⟨1206410245989474886706083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25736751914442130916396437 1206410245989474886706083)
                ·
                  refine ⟨1809615368984212330059125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1206410245989474886706083 1809615368984212330059125)
                  ·
                    refine ⟨169651440842269905943043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1809615368984212330059125 169651440842269905943043)
                    ·
                      rfl

theorem cell23_991185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 6, 1, 5].length) (baseStart_991185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_991185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_991185 prefixEnd_991185 := by exact prefixLift 991185
  have htrace : WordTrace (prefixWord ++ tailWord_991185) baseStart_991185 baseEnd_991185 := by
    simpa [prefixWord, tailWord_991185, baseEnd_991185] using wordTrace_append hprefix tailTrace_991185
  have hstable : (prefixWord ++ tailWord_991185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991185).length < 2 ^ (prefixWord ++ tailWord_991185).sum := by decide
  have hdescent : baseEnd_991185 < baseStart_991185 := by decide
  rcases family_descends (prefixWord ++ tailWord_991185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991216 : List Nat := [2, 1, 1, 1, 3, 2, 6, 2, 1, 1, 3]
def baseStart_991216 : Nat := 118140960795 + 991216 * 2 ^ 59
def prefixEnd_991216 : Nat := 4983230072969 + 3 ^ 40 * 991216 * 2
def baseEnd_991216 : Nat := 508970240427099096541487

theorem tailTrace_991216 : CollatzResearch.WordTrace tailWord_991216 prefixEnd_991216 508970240427099096541487 := by
  unfold tailWord_991216
  simp only [CollatzResearch.WordTrace]
  refine ⟨18076308788500596530172751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24101745051334128706897001 18076308788500596530172751)
  ·
    refine ⟨27114463182750894795259127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18076308788500596530172751 27114463182750894795259127)
    ·
      refine ⟨40671694774126342192888691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27114463182750894795259127 40671694774126342192888691)
      ·
        refine ⟨61007542161189513289333037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40671694774126342192888691 61007542161189513289333037)
        ·
          refine ⟨22877828310446067483499889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61007542161189513289333037 22877828310446067483499889)
          ·
            refine ⟨17158371232834550612624917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22877828310446067483499889 17158371232834550612624917)
            ·
              refine ⟨804298651539119559966793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17158371232834550612624917 804298651539119559966793)
              ·
                refine ⟨603223988654339669975095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 804298651539119559966793 603223988654339669975095)
                ·
                  refine ⟨904835982981509504962643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 603223988654339669975095 904835982981509504962643)
                  ·
                    refine ⟨1357253974472264257443965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 904835982981509504962643 1357253974472264257443965)
                    ·
                      refine ⟨508970240427099096541487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1357253974472264257443965 508970240427099096541487)
                      ·
                        rfl

theorem cell23_991216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 2, 1, 1, 3].length) (baseStart_991216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_991216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_991216 prefixEnd_991216 := by exact prefixLift 991216
  have htrace : WordTrace (prefixWord ++ tailWord_991216) baseStart_991216 baseEnd_991216 := by
    simpa [prefixWord, tailWord_991216, baseEnd_991216] using wordTrace_append hprefix tailTrace_991216
  have hstable : (prefixWord ++ tailWord_991216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991216).length < 2 ^ (prefixWord ++ tailWord_991216).sum := by decide
  have hdescent : baseEnd_991216 < baseStart_991216 := by decide
  rcases family_descends (prefixWord ++ tailWord_991216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991239 : List Nat := [1, 1, 4, 3, 1, 2, 1, 1, 5, 2, 2]
def baseStart_991239 : Nat := 118140960795 + 991239 * 2 ^ 59
def prefixEnd_991239 : Nat := 4983230072969 + 3 ^ 40 * 991239 * 2
def baseEnd_991239 : Nat := 508982050482152506553881

theorem tailTrace_991239 : CollatzResearch.WordTrace tailWord_991239 prefixEnd_991239 508982050482152506553881 := by
  unfold tailWord_991239
  simp only [CollatzResearch.WordTrace]
  refine ⟨36153456455917867988432771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24102304303945245325621847 36153456455917867988432771)
  ·
    refine ⟨54230184683876801982649157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36153456455917867988432771 54230184683876801982649157)
    ·
      refine ⟨10168159628226900371746717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54230184683876801982649157 10168159628226900371746717)
      ·
        refine ⟨3813059860585087639405019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10168159628226900371746717 3813059860585087639405019)
        ·
          refine ⟨5719589790877631459107529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3813059860585087639405019 5719589790877631459107529)
          ·
            refine ⟨4289692343158223594330647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5719589790877631459107529 4289692343158223594330647)
            ·
              refine ⟨6434538514737335391495971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4289692343158223594330647 6434538514737335391495971)
              ·
                refine ⟨9651807772106003087243957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6434538514737335391495971 9651807772106003087243957)
                ·
                  refine ⟨904856978634937789429121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9651807772106003087243957 904856978634937789429121)
                  ·
                    refine ⟨678642733976203342071841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 904856978634937789429121 678642733976203342071841)
                    ·
                      refine ⟨508982050482152506553881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 678642733976203342071841 508982050482152506553881)
                      ·
                        rfl

theorem cell23_991239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_991239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_991239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_991239 prefixEnd_991239 := by exact prefixLift 991239
  have htrace : WordTrace (prefixWord ++ tailWord_991239) baseStart_991239 baseEnd_991239 := by
    simpa [prefixWord, tailWord_991239, baseEnd_991239] using wordTrace_append hprefix tailTrace_991239
  have hstable : (prefixWord ++ tailWord_991239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991239).length < 2 ^ (prefixWord ++ tailWord_991239).sum := by decide
  have hdescent : baseEnd_991239 < baseStart_991239 := by decide
  rcases family_descends (prefixWord ++ tailWord_991239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991295 : List Nat := [1, 1, 2, 2, 3, 1, 2, 2, 2, 3, 4]
def baseStart_991295 : Nat := 118140960795 + 991295 * 2 ^ 59
def prefixEnd_991295 : Nat := 4983230072969 + 3 ^ 40 * 991295 * 2
def baseEnd_991295 : Nat := 509010805398804287453623

theorem tailTrace_991295 : CollatzResearch.WordTrace tailWord_991295 prefixEnd_991295 509010805398804287453623 := by
  unfold tailWord_991295
  simp only [CollatzResearch.WordTrace]
  refine ⟨36155498943714989552471339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24103665962476659701647559 36155498943714989552471339)
  ·
    refine ⟨54233248415572484328707009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36155498943714989552471339 54233248415572484328707009)
    ·
      refine ⟨40674936311679363246530257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54233248415572484328707009 40674936311679363246530257)
      ·
        refine ⟨30506202233759522434897693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40674936311679363246530257 30506202233759522434897693)
        ·
          refine ⟨11439825837659820913086635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30506202233759522434897693 11439825837659820913086635)
          ·
            refine ⟨17159738756489731369629953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11439825837659820913086635 17159738756489731369629953)
            ·
              refine ⟨12869804067367298527222465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17159738756489731369629953 12869804067367298527222465)
              ·
                refine ⟨9652353050525473895416849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12869804067367298527222465 9652353050525473895416849)
                ·
                  refine ⟨7239264787894105421562637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9652353050525473895416849 7239264787894105421562637)
                  ·
                    refine ⟨2714724295460289533085989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7239264787894105421562637 2714724295460289533085989)
                    ·
                      refine ⟨509010805398804287453623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2714724295460289533085989 509010805398804287453623)
                      ·
                        rfl

theorem cell23_991295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 3, 4].length) (baseStart_991295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_991295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_991295 prefixEnd_991295 := by exact prefixLift 991295
  have htrace : WordTrace (prefixWord ++ tailWord_991295) baseStart_991295 baseEnd_991295 := by
    simpa [prefixWord, tailWord_991295, baseEnd_991295] using wordTrace_append hprefix tailTrace_991295
  have hstable : (prefixWord ++ tailWord_991295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991295).length < 2 ^ (prefixWord ++ tailWord_991295).sum := by decide
  have hdescent : baseEnd_991295 < baseStart_991295 := by decide
  rcases family_descends (prefixWord ++ tailWord_991295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991342 : List Nat := [4, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4]
def baseStart_991342 : Nat := 118140960795 + 991342 * 2 ^ 59
def prefixEnd_991342 : Nat := 4983230072969 + 3 ^ 40 * 991342 * 2
def baseEnd_991342 : Nat := 509034938989565603565907

theorem tailTrace_991342 : CollatzResearch.WordTrace tailWord_991342 prefixEnd_991342 509034938989565603565907 := by
  unfold tailWord_991342
  simp only [CollatzResearch.WordTrace]
  refine ⟨4519651646818089572429035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24104808783029811052954853 4519651646818089572429035)
  ·
    refine ⟨6779477470227134358643553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4519651646818089572429035 6779477470227134358643553)
    ·
      refine ⟨5084608102670350768982665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6779477470227134358643553 5084608102670350768982665)
      ·
        refine ⟨3813456077002763076736999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5084608102670350768982665 3813456077002763076736999)
        ·
          refine ⟨5720184115504144615105499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3813456077002763076736999 5720184115504144615105499)
          ·
            refine ⟨8580276173256216922658249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5720184115504144615105499 8580276173256216922658249)
            ·
              refine ⟨6435207129942162691993687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8580276173256216922658249 6435207129942162691993687)
              ·
                refine ⟨9652810694913244037990531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6435207129942162691993687 9652810694913244037990531)
                ·
                  refine ⟨14479216042369866056985797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9652810694913244037990531 14479216042369866056985797)
                  ·
                    refine ⟨2714853007944349885684837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14479216042369866056985797 2714853007944349885684837)
                    ·
                      refine ⟨509034938989565603565907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2714853007944349885684837 509034938989565603565907)
                      ·
                        rfl

theorem cell23_991342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_991342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_991342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_991342 prefixEnd_991342 := by exact prefixLift 991342
  have htrace : WordTrace (prefixWord ++ tailWord_991342) baseStart_991342 baseEnd_991342 := by
    simpa [prefixWord, tailWord_991342, baseEnd_991342] using wordTrace_append hprefix tailTrace_991342
  have hstable : (prefixWord ++ tailWord_991342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991342).length < 2 ^ (prefixWord ++ tailWord_991342).sum := by decide
  have hdescent : baseEnd_991342 < baseStart_991342 := by decide
  rcases family_descends (prefixWord ++ tailWord_991342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991386 : List Nat := [3, 1, 1, 5, 2, 1, 1, 4, 5]
def baseStart_991386 : Nat := 118140960795 + 991386 * 2 ^ 59
def prefixEnd_991386 : Nat := 4983230072969 + 3 ^ 40 * 991386 * 2
def baseEnd_991386 : Nat := 56561948015373714601745

theorem tailTrace_991386 : CollatzResearch.WordTrace tailWord_991386 prefixEnd_991386 56561948015373714601745 := by
  unfold tailWord_991386
  simp only [CollatzResearch.WordTrace]
  refine ⟨9039704496596328023508503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24105878657590208062689341 9039704496596328023508503)
  ·
    refine ⟨13559556744894492035262755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9039704496596328023508503 13559556744894492035262755)
    ·
      refine ⟨20339335117341738052894133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13559556744894492035262755 20339335117341738052894133)
      ·
        refine ⟨1906812667250787942458825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20339335117341738052894133 1906812667250787942458825)
        ·
          refine ⟨1430109500438090956844119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1906812667250787942458825 1430109500438090956844119)
          ·
            refine ⟨2145164250657136435266179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1430109500438090956844119 2145164250657136435266179)
            ·
              refine ⟨3217746375985704652899269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2145164250657136435266179 3217746375985704652899269)
              ·
                refine ⟨603327445497319622418613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3217746375985704652899269 603327445497319622418613)
                ·
                  refine ⟨56561948015373714601745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 603327445497319622418613 56561948015373714601745)
                  ·
                    rfl

theorem cell23_991386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 4, 5].length) (baseStart_991386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_991386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_991386 prefixEnd_991386 := by exact prefixLift 991386
  have htrace : WordTrace (prefixWord ++ tailWord_991386) baseStart_991386 baseEnd_991386 := by
    simpa [prefixWord, tailWord_991386, baseEnd_991386] using wordTrace_append hprefix tailTrace_991386
  have hstable : (prefixWord ++ tailWord_991386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991386).length < 2 ^ (prefixWord ++ tailWord_991386).sum := by decide
  have hdescent : baseEnd_991386 < baseStart_991386 := by decide
  rcases family_descends (prefixWord ++ tailWord_991386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991389 : List Nat := [1, 4, 2, 1, 1, 3, 1, 1, 2, 5, 2]
def baseStart_991389 : Nat := 118140960795 + 991389 * 2 ^ 59
def prefixEnd_991389 : Nat := 4983230072969 + 3 ^ 40 * 991389 * 2
def baseEnd_991389 : Nat := 509059072580326919678191

theorem tailTrace_991389 : CollatzResearch.WordTrace tailWord_991389 prefixEnd_991389 509059072580326919678191 := by
  unfold tailWord_991389
  simp only [CollatzResearch.WordTrace]
  refine ⟨36158927405374443606393221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24105951603582962404262147 36158927405374443606393221)
  ·
    refine ⟨6779798888507708176198729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36158927405374443606393221 6779798888507708176198729)
    ·
      refine ⟨5084849166380781132149047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6779798888507708176198729 5084849166380781132149047)
      ·
        refine ⟨7627273749571171698223571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5084849166380781132149047 7627273749571171698223571)
        ·
          refine ⟨11440910624356757547335357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7627273749571171698223571 11440910624356757547335357)
          ·
            refine ⟨4290341484133784080250759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11440910624356757547335357 4290341484133784080250759)
            ·
              refine ⟨6435512226200676120376139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4290341484133784080250759 6435512226200676120376139)
              ·
                refine ⟨9653268339301014180564209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6435512226200676120376139 9653268339301014180564209)
                ·
                  refine ⟨7239951254475760635423157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9653268339301014180564209 7239951254475760635423157)
                  ·
                    refine ⟨678745430107102559570921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7239951254475760635423157 678745430107102559570921)
                    ·
                      refine ⟨509059072580326919678191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 678745430107102559570921 509059072580326919678191)
                      ·
                        rfl

theorem cell23_991389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 5, 2].length) (baseStart_991389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_991389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_991389 prefixEnd_991389 := by exact prefixLift 991389
  have htrace : WordTrace (prefixWord ++ tailWord_991389) baseStart_991389 baseEnd_991389 := by
    simpa [prefixWord, tailWord_991389, baseEnd_991389] using wordTrace_append hprefix tailTrace_991389
  have hstable : (prefixWord ++ tailWord_991389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991389).length < 2 ^ (prefixWord ++ tailWord_991389).sum := by decide
  have hdescent : baseEnd_991389 < baseStart_991389 := by decide
  rcases family_descends (prefixWord ++ tailWord_991389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991392 : List Nat := [2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 5]
def baseStart_991392 : Nat := 118140960795 + 991392 * 2 ^ 59
def prefixEnd_991392 : Nat := 4983230072969 + 3 ^ 40 * 991392 * 2
def baseEnd_991392 : Nat := 509060613022290407940677

theorem tailTrace_991392 : CollatzResearch.WordTrace tailWord_991392 prefixEnd_991392 509060613022290407940677 := by
  unfold tailWord_991392
  simp only [CollatzResearch.WordTrace]
  refine ⟨18079518412181787559376215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24106024549575716745834953 18079518412181787559376215)
  ·
    refine ⟨27119277618272681339064323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18079518412181787559376215 27119277618272681339064323)
    ·
      refine ⟨40678916427409022008596485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27119277618272681339064323 40678916427409022008596485)
      ·
        refine ⟨7627296830139191626611841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40678916427409022008596485 7627296830139191626611841)
        ·
          refine ⟨5720472622604393719958881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7627296830139191626611841 5720472622604393719958881)
          ·
            refine ⟨4290354466953295289969161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5720472622604393719958881 4290354466953295289969161)
            ·
              refine ⟨3217765850214971467476871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4290354466953295289969161 3217765850214971467476871)
              ·
                refine ⟨4826648775322457201215307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3217765850214971467476871 4826648775322457201215307)
                ·
                  refine ⟨7239973162983685801822961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4826648775322457201215307 7239973162983685801822961)
                  ·
                    refine ⟨5429979872237764351367221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7239973162983685801822961 5429979872237764351367221)
                    ·
                      refine ⟨509060613022290407940677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5429979872237764351367221 509060613022290407940677)
                      ·
                        rfl

theorem cell23_991392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_991392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_991392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_991392 prefixEnd_991392 := by exact prefixLift 991392
  have htrace : WordTrace (prefixWord ++ tailWord_991392) baseStart_991392 baseEnd_991392 := by
    simpa [prefixWord, tailWord_991392, baseEnd_991392] using wordTrace_append hprefix tailTrace_991392
  have hstable : (prefixWord ++ tailWord_991392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991392).length < 2 ^ (prefixWord ++ tailWord_991392).sum := by decide
  have hdescent : baseEnd_991392 < baseStart_991392 := by decide
  rcases family_descends (prefixWord ++ tailWord_991392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991395 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 4, 8]
def baseStart_991395 : Nat := 118140960795 + 991395 * 2 ^ 59
def prefixEnd_991395 : Nat := 4983230072969 + 3 ^ 40 * 991395 * 2
def baseEnd_991395 : Nat := 169687384488084632067721

theorem tailTrace_991395 : CollatzResearch.WordTrace tailWord_991395 prefixEnd_991395 169687384488084632067721 := by
  unfold tailWord_991395
  simp only [CollatzResearch.WordTrace]
  refine ⟨36159146243352706631111639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24106097495568471087407759 36159146243352706631111639)
  ·
    refine ⟨54238719365029059946667459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36159146243352706631111639 54238719365029059946667459)
    ·
      refine ⟨81358079047543589920001189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54238719365029059946667459 81358079047543589920001189)
      ·
        refine ⟨15254639821414423110000223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81358079047543589920001189 15254639821414423110000223)
        ·
          refine ⟨22881959732121634665000335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15254639821414423110000223 22881959732121634665000335)
          ·
            refine ⟨34322939598182451997500503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22881959732121634665000335 34322939598182451997500503)
            ·
              refine ⟨51484409397273677996250755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34322939598182451997500503 51484409397273677996250755)
              ·
                refine ⟨77226614095910516994376133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51484409397273677996250755 77226614095910516994376133)
                ·
                  refine ⟨14479990142983221936445525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77226614095910516994376133 14479990142983221936445525)
                  ·
                    refine ⟨169687384488084632067721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 14479990142983221936445525 169687384488084632067721)
                    ·
                      rfl

theorem cell23_991395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 8].length) (baseStart_991395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_991395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_991395 prefixEnd_991395 := by exact prefixLift 991395
  have htrace : WordTrace (prefixWord ++ tailWord_991395) baseStart_991395 baseEnd_991395 := by
    simpa [prefixWord, tailWord_991395, baseEnd_991395] using wordTrace_append hprefix tailTrace_991395
  have hstable : (prefixWord ++ tailWord_991395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991395).length < 2 ^ (prefixWord ++ tailWord_991395).sum := by decide
  have hdescent : baseEnd_991395 < baseStart_991395 := by decide
  rcases family_descends (prefixWord ++ tailWord_991395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991472 : List Nat := [2, 1, 1, 1, 3, 1, 1, 5, 3, 5]
def baseStart_991472 : Nat := 118140960795 + 991472 * 2 ^ 59
def prefixEnd_991472 : Nat := 4983230072969 + 3 ^ 40 * 991472 * 2
def baseEnd_991472 : Nat := 169700563824883364980103

theorem tailTrace_991472 : CollatzResearch.WordTrace tailWord_991472 prefixEnd_991472 169700563824883364980103 := by
  unfold tailWord_991472
  simp only [CollatzResearch.WordTrace]
  refine ⟨18080977332036874390832335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24107969776049165854443113 18080977332036874390832335)
  ·
    refine ⟨27121465998055311586248503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18080977332036874390832335 27121465998055311586248503)
    ·
      refine ⟨40682198997082967379372755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27121465998055311586248503 40682198997082967379372755)
      ·
        refine ⟨61023298495624451069059133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40682198997082967379372755 61023298495624451069059133)
        ·
          refine ⟨22883736935859169150897175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61023298495624451069059133 22883736935859169150897175)
          ·
            refine ⟨34325605403788753726345763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22883736935859169150897175 34325605403788753726345763)
            ·
              refine ⟨51488408105683130589518645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34325605403788753726345763 51488408105683130589518645)
              ·
                refine ⟨4827038259907793492767373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51488408105683130589518645 4827038259907793492767373)
                ·
                  refine ⟨1810139347465422559787765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4827038259907793492767373 1810139347465422559787765)
                  ·
                    refine ⟨169700563824883364980103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1810139347465422559787765 169700563824883364980103)
                    ·
                      rfl

theorem cell23_991472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 3, 5].length) (baseStart_991472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_991472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_991472 prefixEnd_991472 := by exact prefixLift 991472
  have htrace : WordTrace (prefixWord ++ tailWord_991472) baseStart_991472 baseEnd_991472 := by
    simpa [prefixWord, tailWord_991472, baseEnd_991472] using wordTrace_append hprefix tailTrace_991472
  have hstable : (prefixWord ++ tailWord_991472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991472).length < 2 ^ (prefixWord ++ tailWord_991472).sum := by decide
  have hdescent : baseEnd_991472 < baseStart_991472 := by decide
  rcases family_descends (prefixWord ++ tailWord_991472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991489 : List Nat := [1, 2, 4, 1, 1, 2, 1, 5, 1, 5]
def baseStart_991489 : Nat := 118140960795 + 991489 * 2 ^ 59
def prefixEnd_991489 : Nat := 4983230072969 + 3 ^ 40 * 991489 * 2
def baseEnd_991489 : Nat := 169703473548592176142577

theorem tailTrace_991489 : CollatzResearch.WordTrace tailWord_991489 prefixEnd_991489 169703473548592176142577 := by
  unfold tailWord_991489
  simp only [CollatzResearch.WordTrace]
  refine ⟨36162574705012160685033521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24108383136674773790022347 36162574705012160685033521)
  ·
    refine ⟨27121931028759120513775141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36162574705012160685033521 27121931028759120513775141)
    ·
      refine ⟨5085362067892335096332839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27121931028759120513775141 5085362067892335096332839)
      ·
        refine ⟨7628043101838502644499259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5085362067892335096332839 7628043101838502644499259)
        ·
          refine ⟨11442064652757753966748889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7628043101838502644499259 11442064652757753966748889)
          ·
            refine ⟨8581548489568315475061667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11442064652757753966748889 8581548489568315475061667)
            ·
              refine ⟨12872322734352473212592501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8581548489568315475061667 12872322734352473212592501)
              ·
                refine ⟨1206780256345544363680547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12872322734352473212592501 1206780256345544363680547)
                ·
                  refine ⟨1810170384518316545520821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1206780256345544363680547 1810170384518316545520821)
                  ·
                    refine ⟨169703473548592176142577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1810170384518316545520821 169703473548592176142577)
                    ·
                      rfl

theorem cell23_991489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_991489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_991489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_991489 prefixEnd_991489 := by exact prefixLift 991489
  have htrace : WordTrace (prefixWord ++ tailWord_991489) baseStart_991489 baseEnd_991489 := by
    simpa [prefixWord, tailWord_991489, baseEnd_991489] using wordTrace_append hprefix tailTrace_991489
  have hstable : (prefixWord ++ tailWord_991489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991489).length < 2 ^ (prefixWord ++ tailWord_991489).sum := by decide
  have hdescent : baseEnd_991489 < baseStart_991489 := by decide
  rcases family_descends (prefixWord ++ tailWord_991489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991496 : List Nat := [2, 1, 3, 2, 3, 1, 1, 1, 4, 3, 2]
def baseStart_991496 : Nat := 118140960795 + 991496 * 2 ^ 59
def prefixEnd_991496 : Nat := 4983230072969 + 3 ^ 40 * 991496 * 2
def baseEnd_991496 : Nat := 509114015010358001040199

theorem tailTrace_991496 : CollatzResearch.WordTrace tailWord_991496 prefixEnd_991496 509114015010358001040199 := by
  unfold tailWord_991496
  simp only [CollatzResearch.WordTrace]
  refine ⟨18081415007993400440269171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24108553343991200587025561 18081415007993400440269171)
  ·
    refine ⟨27122122511990100660403757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18081415007993400440269171 27122122511990100660403757)
    ·
      refine ⟨10170795941996287747651409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27122122511990100660403757 10170795941996287747651409)
      ·
        refine ⟨7628096956497215810738557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10170795941996287747651409 7628096956497215810738557)
        ·
          refine ⟨2860536358686455929026959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7628096956497215810738557 2860536358686455929026959)
          ·
            refine ⟨4290804538029683893540439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2860536358686455929026959 4290804538029683893540439)
            ·
              refine ⟨6436206807044525840310659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4290804538029683893540439 6436206807044525840310659)
              ·
                refine ⟨9654310210566788760465989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6436206807044525840310659 9654310210566788760465989)
                ·
                  refine ⟨1810183164481272892587373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9654310210566788760465989 1810183164481272892587373)
                  ·
                    refine ⟨678818686680477334720265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1810183164481272892587373 678818686680477334720265)
                    ·
                      refine ⟨509114015010358001040199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 678818686680477334720265 509114015010358001040199)
                      ·
                        rfl

theorem cell23_991496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 4, 3, 2].length) (baseStart_991496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_991496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_991496 prefixEnd_991496 := by exact prefixLift 991496
  have htrace : WordTrace (prefixWord ++ tailWord_991496) baseStart_991496 baseEnd_991496 := by
    simpa [prefixWord, tailWord_991496, baseEnd_991496] using wordTrace_append hprefix tailTrace_991496
  have hstable : (prefixWord ++ tailWord_991496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991496).length < 2 ^ (prefixWord ++ tailWord_991496).sum := by decide
  have hdescent : baseEnd_991496 < baseStart_991496 := by decide
  rcases family_descends (prefixWord ++ tailWord_991496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991530 : List Nat := [3, 1, 4, 2, 2, 1, 2, 1, 2, 3, 2]
def baseStart_991530 : Nat := 118140960795 + 991530 * 2 ^ 59
def prefixEnd_991530 : Nat := 4983230072969 + 3 ^ 40 * 991530 * 2
def baseEnd_991530 : Nat := 509131473352610868015043

theorem tailTrace_991530 : CollatzResearch.WordTrace tailWord_991530 prefixEnd_991530 509131473352610868015043 := by
  unfold tailWord_991530
  simp only [CollatzResearch.WordTrace]
  refine ⟨9041017524465906171819011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24109380065242416458184029 9041017524465906171819011)
  ·
    refine ⟨13561526286698859257728517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9041017524465906171819011 13561526286698859257728517)
    ·
      refine ⟨2542786178756036110824097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13561526286698859257728517 2542786178756036110824097)
      ·
        refine ⟨1907089634067027083118073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2542786178756036110824097 1907089634067027083118073)
        ·
          refine ⟨1430317225550270312338555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1907089634067027083118073 1430317225550270312338555)
          ·
            refine ⟨2145475838325405468507833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1430317225550270312338555 2145475838325405468507833)
            ·
              refine ⟨1609106878744054101380875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2145475838325405468507833 1609106878744054101380875)
              ·
                refine ⟨2413660318116081152071313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1609106878744054101380875 2413660318116081152071313)
                ·
                  refine ⟨1810245238587060864053485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2413660318116081152071313 1810245238587060864053485)
                  ·
                    refine ⟨678841964470147824020057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1810245238587060864053485 678841964470147824020057)
                    ·
                      refine ⟨509131473352610868015043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 678841964470147824020057 509131473352610868015043)
                      ·
                        rfl

theorem cell23_991530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_991530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_991530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_991530 prefixEnd_991530 := by exact prefixLift 991530
  have htrace : WordTrace (prefixWord ++ tailWord_991530) baseStart_991530 baseEnd_991530 := by
    simpa [prefixWord, tailWord_991530, baseEnd_991530] using wordTrace_append hprefix tailTrace_991530
  have hstable : (prefixWord ++ tailWord_991530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991530).length < 2 ^ (prefixWord ++ tailWord_991530).sum := by decide
  have hdescent : baseEnd_991530 < baseStart_991530 := by decide
  rcases family_descends (prefixWord ++ tailWord_991530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991532 : List Nat := [2, 2, 1, 1, 1, 3, 4, 9]
def baseStart_991532 : Nat := 118140960795 + 991532 * 2 ^ 59
def prefixEnd_991532 : Nat := 4983230072969 + 3 ^ 40 * 991532 * 2
def baseEnd_991532 : Nat := 18856759270885920747779

theorem tailTrace_991532 : CollatzResearch.WordTrace tailWord_991532 prefixEnd_991532 18856759270885920747779 := by
  unfold tailWord_991532
  simp only [CollatzResearch.WordTrace]
  refine ⟨18082071521928189514424425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24109428695904252685899233 18082071521928189514424425)
  ·
    refine ⟨13561553641446142135818319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18082071521928189514424425 13561553641446142135818319)
    ·
      refine ⟨20342330462169213203727479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13561553641446142135818319 20342330462169213203727479)
      ·
        refine ⟨30513495693253819805591219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20342330462169213203727479 30513495693253819805591219)
        ·
          refine ⟨45770243539880729708386829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30513495693253819805591219 45770243539880729708386829)
          ·
            refine ⟨17163841327455273640645061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45770243539880729708386829 17163841327455273640645061)
            ·
              refine ⟨3218220248897863807620949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17163841327455273640645061 3218220248897863807620949)
              ·
                refine ⟨18856759270885920747779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3218220248897863807620949 18856759270885920747779)
                ·
                  rfl

theorem cell23_991532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 9].length) (baseStart_991532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_991532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_991532 prefixEnd_991532 := by exact prefixLift 991532
  have htrace : WordTrace (prefixWord ++ tailWord_991532) baseStart_991532 baseEnd_991532 := by
    simpa [prefixWord, tailWord_991532, baseEnd_991532] using wordTrace_append hprefix tailTrace_991532
  have hstable : (prefixWord ++ tailWord_991532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991532).length < 2 ^ (prefixWord ++ tailWord_991532).sum := by decide
  have hdescent : baseEnd_991532 < baseStart_991532 := by decide
  rcases family_descends (prefixWord ++ tailWord_991532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991539 : List Nat := [1, 1, 1, 2, 5, 1, 3, 2, 1, 2, 4]
def baseStart_991539 : Nat := 118140960795 + 991539 * 2 ^ 59
def prefixEnd_991539 : Nat := 4983230072969 + 3 ^ 40 * 991539 * 2
def baseEnd_991539 : Nat := 509136094678501332802501

theorem tailTrace_991539 : CollatzResearch.WordTrace tailWord_991539 prefixEnd_991539 509136094678501332802501 := by
  unfold tailWord_991539
  simp only [CollatzResearch.WordTrace]
  refine ⟨36164398354831019224353671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24109598903220679482902447 36164398354831019224353671)
  ·
    refine ⟨54246597532246528836530507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36164398354831019224353671 54246597532246528836530507)
    ·
      refine ⟨81369896298369793254795761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54246597532246528836530507 81369896298369793254795761)
      ·
        refine ⟨61027422223777344941096821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81369896298369793254795761 61027422223777344941096821)
        ·
          refine ⟨5721320833479126088227827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61027422223777344941096821 5721320833479126088227827)
          ·
            refine ⟨8581981250218689132341741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5721320833479126088227827 8581981250218689132341741)
            ·
              refine ⟨3218242968832008424628153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8581981250218689132341741 3218242968832008424628153)
              ·
                refine ⟨2413682226624006318471115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3218242968832008424628153 2413682226624006318471115)
                ·
                  refine ⟨3620523339936009477706673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2413682226624006318471115 3620523339936009477706673)
                  ·
                    refine ⟨2715392504952007108280005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3620523339936009477706673 2715392504952007108280005)
                    ·
                      refine ⟨509136094678501332802501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2715392504952007108280005 509136094678501332802501)
                      ·
                        rfl

theorem cell23_991539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 2, 4].length) (baseStart_991539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_991539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_991539 prefixEnd_991539 := by exact prefixLift 991539
  have htrace : WordTrace (prefixWord ++ tailWord_991539) baseStart_991539 baseEnd_991539 := by
    simpa [prefixWord, tailWord_991539, baseEnd_991539] using wordTrace_append hprefix tailTrace_991539
  have hstable : (prefixWord ++ tailWord_991539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991539).length < 2 ^ (prefixWord ++ tailWord_991539).sum := by decide
  have hdescent : baseEnd_991539 < baseStart_991539 := by decide
  rcases family_descends (prefixWord ++ tailWord_991539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991546 : List Nat := [3, 1, 1, 1, 4, 4, 1, 1, 1, 1, 5]
def baseStart_991546 : Nat := 118140960795 + 991546 * 2 ^ 59
def prefixEnd_991546 : Nat := 4983230072969 + 3 ^ 40 * 991546 * 2
def baseEnd_991546 : Nat := 509139689043082805414969

theorem tailTrace_991546 : CollatzResearch.WordTrace tailWord_991546 prefixEnd_991546 509139689043082805414969 := by
  unfold tailWord_991546
  simp only [CollatzResearch.WordTrace]
  refine ⟨9041163416451414854964623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24109769110537106279905661 9041163416451414854964623)
  ·
    refine ⟨13561745124677122282446935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9041163416451414854964623 13561745124677122282446935)
    ·
      refine ⟨20342617687015683423670403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13561745124677122282446935 20342617687015683423670403)
      ·
        refine ⟨30513926530523525135505605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20342617687015683423670403 30513926530523525135505605)
        ·
          refine ⟨5721361224473160962907301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30513926530523525135505605 5721361224473160962907301)
          ·
            refine ⟨1072755229588717680545119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5721361224473160962907301 1072755229588717680545119)
            ·
              refine ⟨1609132844383076520817679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1072755229588717680545119 1609132844383076520817679)
              ·
                refine ⟨2413699266574614781226519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1609132844383076520817679 2413699266574614781226519)
                ·
                  refine ⟨3620548899861922171839779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2413699266574614781226519 3620548899861922171839779)
                  ·
                    refine ⟨5430823349792883257759669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3620548899861922171839779 5430823349792883257759669)
                    ·
                      refine ⟨509139689043082805414969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5430823349792883257759669 509139689043082805414969)
                      ·
                        rfl

theorem cell23_991546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 1, 1, 5].length) (baseStart_991546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_991546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_991546 prefixEnd_991546 := by exact prefixLift 991546
  have htrace : WordTrace (prefixWord ++ tailWord_991546) baseStart_991546 baseEnd_991546 := by
    simpa [prefixWord, tailWord_991546, baseEnd_991546] using wordTrace_append hprefix tailTrace_991546
  have hstable : (prefixWord ++ tailWord_991546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991546).length < 2 ^ (prefixWord ++ tailWord_991546).sum := by decide
  have hdescent : baseEnd_991546 < baseStart_991546 := by decide
  rcases family_descends (prefixWord ++ tailWord_991546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991552 : List Nat := [2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 6]
def baseStart_991552 : Nat := 118140960795 + 991552 * 2 ^ 59
def prefixEnd_991552 : Nat := 4983230072969 + 3 ^ 40 * 991552 * 2
def baseEnd_991552 : Nat := 509142769927009781939941

theorem tailTrace_991552 : CollatzResearch.WordTrace tailWord_991552 prefixEnd_991552 509142769927009781939941 := by
  unfold tailWord_991552
  simp only [CollatzResearch.WordTrace]
  refine ⟨18082436251891961222288455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24109915002522614963051273 18082436251891961222288455)
  ·
    refine ⟨27123654377837941833432683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18082436251891961222288455 27123654377837941833432683)
    ·
      refine ⟨40685481566756912750149025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27123654377837941833432683 40685481566756912750149025)
      ·
        refine ⟨30514111175067684562611769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40685481566756912750149025 30514111175067684562611769)
        ·
          refine ⟨22885583381300763421958827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30514111175067684562611769 22885583381300763421958827)
          ·
            refine ⟨34328375071951145132938241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22885583381300763421958827 34328375071951145132938241)
            ·
              refine ⟨25746281303963358849703681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34328375071951145132938241 25746281303963358849703681)
              ·
                refine ⟨19309710977972519137277761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25746281303963358849703681 19309710977972519137277761)
                ·
                  refine ⟨14482283233479389352958321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19309710977972519137277761 14482283233479389352958321)
                  ·
                    refine ⟨10861712425109542014718741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14482283233479389352958321 10861712425109542014718741)
                    ·
                      refine ⟨509142769927009781939941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10861712425109542014718741 509142769927009781939941)
                      ·
                        rfl

theorem cell23_991552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 6].length) (baseStart_991552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_991552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_991552 prefixEnd_991552 := by exact prefixLift 991552
  have htrace : WordTrace (prefixWord ++ tailWord_991552) baseStart_991552 baseEnd_991552 := by
    simpa [prefixWord, tailWord_991552, baseEnd_991552] using wordTrace_append hprefix tailTrace_991552
  have hstable : (prefixWord ++ tailWord_991552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991552).length < 2 ^ (prefixWord ++ tailWord_991552).sum := by decide
  have hdescent : baseEnd_991552 < baseStart_991552 := by decide
  rcases family_descends (prefixWord ++ tailWord_991552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991559 : List Nat := [1, 1, 4, 1, 2, 2, 1, 2, 3, 3, 3]
def baseStart_991559 : Nat := 118140960795 + 991559 * 2 ^ 59
def prefixEnd_991559 : Nat := 4983230072969 + 3 ^ 40 * 991559 * 2
def baseEnd_991559 : Nat := 509146364291591254552409

theorem tailTrace_991559 : CollatzResearch.WordTrace tailWord_991559 prefixEnd_991559 509146364291591254552409 := by
  unfold tailWord_991559
  simp only [CollatzResearch.WordTrace]
  refine ⟨36165127814758562640081731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24110085209839041760054487 36165127814758562640081731)
  ·
    refine ⟨54247691722137843960122597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36165127814758562640081731 54247691722137843960122597)
    ·
      refine ⟨10171442197900845742522987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54247691722137843960122597 10171442197900845742522987)
      ·
        refine ⟨15257163296851268613784481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10171442197900845742522987 15257163296851268613784481)
        ·
          refine ⟨11442872472638451460338361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15257163296851268613784481 11442872472638451460338361)
          ·
            refine ⟨8582154354478838595253771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11442872472638451460338361 8582154354478838595253771)
            ·
              refine ⟨12873231531718257892880657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8582154354478838595253771 12873231531718257892880657)
              ·
                refine ⟨9654923648788693419660493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12873231531718257892880657 9654923648788693419660493)
                ·
                  refine ⟨3620596368295760032372685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9654923648788693419660493 3620596368295760032372685)
                  ·
                    refine ⟨1357723638110910012139757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3620596368295760032372685 1357723638110910012139757)
                    ·
                      refine ⟨509146364291591254552409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1357723638110910012139757 509146364291591254552409)
                      ·
                        rfl

theorem cell23_991559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 3, 3].length) (baseStart_991559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_991559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_991559 prefixEnd_991559 := by exact prefixLift 991559
  have htrace : WordTrace (prefixWord ++ tailWord_991559) baseStart_991559 baseEnd_991559 := by
    simpa [prefixWord, tailWord_991559, baseEnd_991559] using wordTrace_append hprefix tailTrace_991559
  have hstable : (prefixWord ++ tailWord_991559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991559).length < 2 ^ (prefixWord ++ tailWord_991559).sum := by decide
  have hdescent : baseEnd_991559 < baseStart_991559 := by decide
  rcases family_descends (prefixWord ++ tailWord_991559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991639 : List Nat := [1, 1, 3, 3, 1, 1, 4, 2, 7]
def baseStart_991639 : Nat := 118140960795 + 991639 * 2 ^ 59
def prefixEnd_991639 : Nat := 4983230072969 + 3 ^ 40 * 991639 * 2
def baseEnd_991639 : Nat := 56576382527105660172449

theorem tailTrace_991639 : CollatzResearch.WordTrace tailWord_991639 prefixEnd_991639 56576382527105660172449 := by
  unfold tailWord_991639
  simp only [CollatzResearch.WordTrace]
  refine ⟨36168045654468736302993971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24112030436312490868662647 36168045654468736302993971)
  ·
    refine ⟨54252068481703104454490957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36168045654468736302993971 54252068481703104454490957)
    ·
      refine ⟨20344525680638664170434109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54252068481703104454490957 20344525680638664170434109)
      ·
        refine ⟨7629197130239499063912791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20344525680638664170434109 7629197130239499063912791)
        ·
          refine ⟨11443795695359248595869187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7629197130239499063912791 11443795695359248595869187)
          ·
            refine ⟨17165693543038872893803781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11443795695359248595869187 17165693543038872893803781)
            ·
              refine ⟨3218567539319788667588209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17165693543038872893803781 3218567539319788667588209)
              ·
                refine ⟨2413925654489841500691157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3218567539319788667588209 2413925654489841500691157)
                ·
                  refine ⟨56576382527105660172449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2413925654489841500691157 56576382527105660172449)
                  ·
                    rfl

theorem cell23_991639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 7].length) (baseStart_991639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_991639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_991639 prefixEnd_991639 := by exact prefixLift 991639
  have htrace : WordTrace (prefixWord ++ tailWord_991639) baseStart_991639 baseEnd_991639 := by
    simpa [prefixWord, tailWord_991639, baseEnd_991639] using wordTrace_append hprefix tailTrace_991639
  have hstable : (prefixWord ++ tailWord_991639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991639).length < 2 ^ (prefixWord ++ tailWord_991639).sum := by decide
  have hdescent : baseEnd_991639 < baseStart_991639 := by decide
  rcases family_descends (prefixWord ++ tailWord_991639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991689 : List Nat := [1, 2, 1, 1, 2, 1, 4, 1, 3, 3, 4]
def baseStart_991689 : Nat := 118140960795 + 991689 * 2 ^ 59
def prefixEnd_991689 : Nat := 4983230072969 + 3 ^ 40 * 991689 * 2
def baseEnd_991689 : Nat := 509213116776675745926811

theorem tailTrace_991689 : CollatzResearch.WordTrace tailWord_991689 prefixEnd_991689 509213116776675745926811 := by
  unfold tailWord_991689
  simp only [CollatzResearch.WordTrace]
  refine ⟨36169869304287594842314121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24113246202858396561542747 36169869304287594842314121)
  ·
    refine ⟨27127401978215696131735591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36169869304287594842314121 27127401978215696131735591)
    ·
      refine ⟨40691102967323544197603387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27127401978215696131735591 40691102967323544197603387)
      ·
        refine ⟨61036654450985316296405081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40691102967323544197603387 61036654450985316296405081)
        ·
          refine ⟨45777490838238987222303811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61036654450985316296405081 45777490838238987222303811)
          ·
            refine ⟨68666236257358480833455717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45777490838238987222303811 68666236257358480833455717)
            ·
              refine ⟨12874919298254715156272947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68666236257358480833455717 12874919298254715156272947)
              ·
                refine ⟨19312378947382072734409421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12874919298254715156272947 19312378947382072734409421)
                ·
                  refine ⟨7242142105268277275403533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19312378947382072734409421 7242142105268277275403533)
                  ·
                    refine ⟨2715803289475603978276325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7242142105268277275403533 2715803289475603978276325)
                    ·
                      refine ⟨509213116776675745926811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2715803289475603978276325 509213116776675745926811)
                      ·
                        rfl

theorem cell23_991689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 3, 4].length) (baseStart_991689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_991689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_991689 prefixEnd_991689 := by exact prefixLift 991689
  have htrace : WordTrace (prefixWord ++ tailWord_991689) baseStart_991689 baseEnd_991689 := by
    simpa [prefixWord, tailWord_991689, baseEnd_991689] using wordTrace_append hprefix tailTrace_991689
  have hstable : (prefixWord ++ tailWord_991689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991689).length < 2 ^ (prefixWord ++ tailWord_991689).sum := by decide
  have hdescent : baseEnd_991689 < baseStart_991689 := by decide
  rcases family_descends (prefixWord ++ tailWord_991689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991757 : List Nat := [1, 7, 1, 1, 1, 1, 3, 1, 2, 1, 4]
def baseStart_991757 : Nat := 118140960795 + 991757 * 2 ^ 59
def prefixEnd_991757 : Nat := 4983230072969 + 3 ^ 40 * 991757 * 2
def baseEnd_991757 : Nat := 509248033461181479876499

theorem tailTrace_991757 : CollatzResearch.WordTrace tailWord_991757 prefixEnd_991757 509248033461181479876499 := by
  unfold tailWord_991757
  simp only [CollatzResearch.WordTrace]
  refine ⟨36172349468041242455789525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24114899645360828303859683 36172349468041242455789525)
  ·
    refine ⟨847789440657216620057567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 36172349468041242455789525 847789440657216620057567)
    ·
      refine ⟨1271684160985824930086351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 847789440657216620057567 1271684160985824930086351)
      ·
        refine ⟨1907526241478737395129527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1271684160985824930086351 1907526241478737395129527)
        ·
          refine ⟨2861289362218106092694291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1907526241478737395129527 2861289362218106092694291)
          ·
            refine ⟨4291934043327159139041437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2861289362218106092694291 4291934043327159139041437)
            ·
              refine ⟨1609475266247684677140539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4291934043327159139041437 1609475266247684677140539)
              ·
                refine ⟨2414212899371527015710809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1609475266247684677140539 2414212899371527015710809)
                ·
                  refine ⟨1810659674528645261783107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2414212899371527015710809 1810659674528645261783107)
                  ·
                    refine ⟨2715989511792967892674661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1810659674528645261783107 2715989511792967892674661)
                    ·
                      refine ⟨509248033461181479876499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2715989511792967892674661 509248033461181479876499)
                      ·
                        rfl

theorem cell23_991757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_991757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_991757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_991757 prefixEnd_991757 := by exact prefixLift 991757
  have htrace : WordTrace (prefixWord ++ tailWord_991757) baseStart_991757 baseEnd_991757 := by
    simpa [prefixWord, tailWord_991757, baseEnd_991757] using wordTrace_append hprefix tailTrace_991757
  have hstable : (prefixWord ++ tailWord_991757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991757).length < 2 ^ (prefixWord ++ tailWord_991757).sum := by decide
  have hdescent : baseEnd_991757 < baseStart_991757 := by decide
  rcases family_descends (prefixWord ++ tailWord_991757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991769 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 1, 3, 7]
def baseStart_991769 : Nat := 118140960795 + 991769 * 2 ^ 59
def prefixEnd_991769 : Nat := 4983230072969 + 3 ^ 40 * 991769 * 2
def baseEnd_991769 : Nat := 509254195229035432926443

theorem tailTrace_991769 : CollatzResearch.WordTrace tailWord_991769 prefixEnd_991769 509254195229035432926443 := by
  unfold tailWord_991769
  simp only [CollatzResearch.WordTrace]
  refine ⟨36172787143997768505226361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24115191429331845670150907 36172787143997768505226361)
  ·
    refine ⟨27129590357998326378919771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36172787143997768505226361 27129590357998326378919771)
    ·
      refine ⟨40694385536997489568379657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27129590357998326378919771 40694385536997489568379657)
      ·
        refine ⟨30520789152748117176284743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40694385536997489568379657 30520789152748117176284743)
        ·
          refine ⟨45781183729122175764427115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30520789152748117176284743 45781183729122175764427115)
          ·
            refine ⟨68671775593683263646640673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45781183729122175764427115 68671775593683263646640673)
            ·
              refine ⟨51503831695262447734980505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68671775593683263646640673 51503831695262447734980505)
              ·
                refine ⟨38627873771446835801235379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51503831695262447734980505 38627873771446835801235379)
                ·
                  refine ⟨57941810657170253701853069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38627873771446835801235379 57941810657170253701853069)
                  ·
                    refine ⟨21728178996438845138194901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57941810657170253701853069 21728178996438845138194901)
                    ·
                      refine ⟨509254195229035432926443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 21728178996438845138194901 509254195229035432926443)
                      ·
                        rfl

theorem cell23_991769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 3, 7].length) (baseStart_991769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_991769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_991769 prefixEnd_991769 := by exact prefixLift 991769
  have htrace : WordTrace (prefixWord ++ tailWord_991769) baseStart_991769 baseEnd_991769 := by
    simpa [prefixWord, tailWord_991769, baseEnd_991769] using wordTrace_append hprefix tailTrace_991769
  have hstable : (prefixWord ++ tailWord_991769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991769).length < 2 ^ (prefixWord ++ tailWord_991769).sum := by decide
  have hdescent : baseEnd_991769 < baseStart_991769 := by decide
  rcases family_descends (prefixWord ++ tailWord_991769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991813 : List Nat := [1, 3, 1, 1, 1, 5, 1, 4, 1, 1, 4]
def baseStart_991813 : Nat := 118140960795 + 991813 * 2 ^ 59
def prefixEnd_991813 : Nat := 4983230072969 + 3 ^ 40 * 991813 * 2
def baseEnd_991813 : Nat := 509276788377833260776241

theorem tailTrace_991813 : CollatzResearch.WordTrace tailWord_991813 prefixEnd_991813 509276788377833260776241 := by
  unfold tailWord_991813
  simp only [CollatzResearch.WordTrace]
  refine ⟨36174391955838364019828093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24116261303892242679885395 36174391955838364019828093)
  ·
    refine ⟨13565396983439386507435535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36174391955838364019828093 13565396983439386507435535)
    ·
      refine ⟨20348095475159079761153303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13565396983439386507435535 20348095475159079761153303)
      ·
        refine ⟨30522143212738619641729955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20348095475159079761153303 30522143212738619641729955)
        ·
          refine ⟨45783214819107929462594933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30522143212738619641729955 45783214819107929462594933)
          ·
            refine ⟨4292176389291368387118275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45783214819107929462594933 4292176389291368387118275)
            ·
              refine ⟨6438264583937052580677413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4292176389291368387118275 6438264583937052580677413)
              ·
                refine ⟨1207174609488197358877015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6438264583937052580677413 1207174609488197358877015)
                ·
                  refine ⟨1810761914232296038315523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1207174609488197358877015 1810761914232296038315523)
                  ·
                    refine ⟨2716142871348444057473285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1810761914232296038315523 2716142871348444057473285)
                    ·
                      refine ⟨509276788377833260776241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2716142871348444057473285 509276788377833260776241)
                      ·
                        rfl

theorem cell23_991813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 4, 1, 1, 4].length) (baseStart_991813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_991813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_991813 prefixEnd_991813 := by exact prefixLift 991813
  have htrace : WordTrace (prefixWord ++ tailWord_991813) baseStart_991813 baseEnd_991813 := by
    simpa [prefixWord, tailWord_991813, baseEnd_991813] using wordTrace_append hprefix tailTrace_991813
  have hstable : (prefixWord ++ tailWord_991813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991813).length < 2 ^ (prefixWord ++ tailWord_991813).sum := by decide
  have hdescent : baseEnd_991813 < baseStart_991813 := by decide
  rcases family_descends (prefixWord ++ tailWord_991813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991816 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 2, 6, 3]
def baseStart_991816 : Nat := 118140960795 + 991816 * 2 ^ 59
def prefixEnd_991816 : Nat := 4983230072969 + 3 ^ 40 * 991816 * 2
def baseEnd_991816 : Nat := 509278328819796749038727

theorem tailTrace_991816 : CollatzResearch.WordTrace tailWord_991816 prefixEnd_991816 509278328819796749038727 := by
  unfold tailWord_991816
  simp only [CollatzResearch.WordTrace]
  refine ⟨18087250687413747766093651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24116334249884997021458201 18087250687413747766093651)
  ·
    refine ⟨27130876031120621649140477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18087250687413747766093651 27130876031120621649140477)
    ·
      refine ⟨10174078511670233118427679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27130876031120621649140477 10174078511670233118427679)
      ·
        refine ⟨15261117767505349677641519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10174078511670233118427679 15261117767505349677641519)
        ·
          refine ⟨22891676651258024516462279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15261117767505349677641519 22891676651258024516462279)
          ·
            refine ⟨34337514976887036774693419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22891676651258024516462279 34337514976887036774693419)
            ·
              refine ⟨51506272465330555162040129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34337514976887036774693419 51506272465330555162040129)
              ·
                refine ⟨38629704348997916371530097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51506272465330555162040129 38629704348997916371530097)
                ·
                  refine ⟨28972278261748437278647573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38629704348997916371530097 28972278261748437278647573)
                  ·
                    refine ⟨1358075543519457997436605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28972278261748437278647573 1358075543519457997436605)
                    ·
                      refine ⟨509278328819796749038727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1358075543519457997436605 509278328819796749038727)
                      ·
                        rfl

theorem cell23_991816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 2, 6, 3].length) (baseStart_991816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_991816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_991816 prefixEnd_991816 := by exact prefixLift 991816
  have htrace : WordTrace (prefixWord ++ tailWord_991816) baseStart_991816 baseEnd_991816 := by
    simpa [prefixWord, tailWord_991816, baseEnd_991816] using wordTrace_append hprefix tailTrace_991816
  have hstable : (prefixWord ++ tailWord_991816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991816).length < 2 ^ (prefixWord ++ tailWord_991816).sum := by decide
  have hdescent : baseEnd_991816 < baseStart_991816 := by decide
  rcases family_descends (prefixWord ++ tailWord_991816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991853 : List Nat := [1, 5, 1, 1, 3, 2, 2, 8]
def baseStart_991853 : Nat := 118140960795 + 991853 * 2 ^ 59
def prefixEnd_991853 : Nat := 4983230072969 + 3 ^ 40 * 991853 * 2
def baseEnd_991853 : Nat := 18862863985333818676891

theorem tailTrace_991853 : CollatzResearch.WordTrace tailWord_991853 prefixEnd_991853 18862863985333818676891 := by
  unfold tailWord_991853
  simp only [CollatzResearch.WordTrace]
  refine ⟨36175850875693450851284213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24117233917128967234189475 36175850875693450851284213)
  ·
    refine ⟨3391486019596261017307895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36175850875693450851284213 3391486019596261017307895)
    ·
      refine ⟨5087229029394391525961843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3391486019596261017307895 5087229029394391525961843)
      ·
        refine ⟨7630843544091587288942765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5087229029394391525961843 7630843544091587288942765)
        ·
          refine ⟨2861566329034345233353537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7630843544091587288942765 2861566329034345233353537)
          ·
            refine ⟨2146174746775758925015153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2861566329034345233353537 2146174746775758925015153)
            ·
              refine ⟨1609631060081819193761365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2146174746775758925015153 1609631060081819193761365)
              ·
                refine ⟨18862863985333818676891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1609631060081819193761365 18862863985333818676891)
                ·
                  rfl

theorem cell23_991853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 8].length) (baseStart_991853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_991853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_991853 prefixEnd_991853 := by exact prefixLift 991853
  have htrace : WordTrace (prefixWord ++ tailWord_991853) baseStart_991853 baseEnd_991853 := by
    simpa [prefixWord, tailWord_991853, baseEnd_991853] using wordTrace_append hprefix tailTrace_991853
  have hstable : (prefixWord ++ tailWord_991853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991853).length < 2 ^ (prefixWord ++ tailWord_991853).sum := by decide
  have hdescent : baseEnd_991853 < baseStart_991853 := by decide
  rcases family_descends (prefixWord ++ tailWord_991853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991874 : List Nat := [3, 4, 3, 1, 1, 1, 1, 2, 1, 6]
def baseStart_991874 : Nat := 118140960795 + 991874 * 2 ^ 59
def prefixEnd_991874 : Nat := 4983230072969 + 3 ^ 40 * 991874 * 2
def baseEnd_991874 : Nat := 169769370232585840704487

theorem tailTrace_991874 : CollatzResearch.WordTrace tailWord_991874 prefixEnd_991874 169769370232585840704487 := by
  unfold tailWord_991874
  simp only [CollatzResearch.WordTrace]
  refine ⟨9044154202154342859449669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24117744539078247625199117 9044154202154342859449669)
  ·
    refine ⟨1695778912903939286146813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9044154202154342859449669 1695778912903939286146813)
    ·
      refine ⟨635917092338977232305055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1695778912903939286146813 635917092338977232305055)
      ·
        refine ⟨953875638508465848457583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 635917092338977232305055 953875638508465848457583)
        ·
          refine ⟨1430813457762698772686375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 953875638508465848457583 1430813457762698772686375)
          ·
            refine ⟨2146220186644048159029563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1430813457762698772686375 2146220186644048159029563)
            ·
              refine ⟨3219330279966072238544345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2146220186644048159029563 3219330279966072238544345)
              ·
                refine ⟨2414497709974554178908259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3219330279966072238544345 2414497709974554178908259)
                ·
                  refine ⟨3621746564961831268362389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2414497709974554178908259 3621746564961831268362389)
                  ·
                    refine ⟨169769370232585840704487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3621746564961831268362389 169769370232585840704487)
                    ·
                      rfl

theorem cell23_991874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_991874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_991874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_991874 prefixEnd_991874 := by exact prefixLift 991874
  have htrace : WordTrace (prefixWord ++ tailWord_991874) baseStart_991874 baseEnd_991874 := by
    simpa [prefixWord, tailWord_991874, baseEnd_991874] using wordTrace_append hprefix tailTrace_991874
  have hstable : (prefixWord ++ tailWord_991874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991874).length < 2 ^ (prefixWord ++ tailWord_991874).sum := by decide
  have hdescent : baseEnd_991874 < baseStart_991874 := by decide
  rcases family_descends (prefixWord ++ tailWord_991874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991914 : List Nat := [3, 1, 5, 2, 1, 1, 2, 1, 1, 3, 3]
def baseStart_991914 : Nat := 118140960795 + 991914 * 2 ^ 59
def prefixEnd_991914 : Nat := 4983230072969 + 3 ^ 40 * 991914 * 2
def baseEnd_991914 : Nat := 509328649923937365613277

theorem tailTrace_991914 : CollatzResearch.WordTrace tailWord_991914 prefixEnd_991914 509328649923937365613277 := by
  unfold tailWord_991914
  simp only [CollatzResearch.WordTrace]
  refine ⟨9044518932118114567313699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24118717152314972179503197 9044518932118114567313699)
  ·
    refine ⟨13566778398177171850970549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9044518932118114567313699 13566778398177171850970549)
    ·
      refine ⟨1271885474829109861028489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13566778398177171850970549 1271885474829109861028489)
      ·
        refine ⟨953914106121832395771367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1271885474829109861028489 953914106121832395771367)
        ·
          refine ⟨1430871159182748593657051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 953914106121832395771367 1430871159182748593657051)
          ·
            refine ⟨2146306738774122890485577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1430871159182748593657051 2146306738774122890485577)
            ·
              refine ⟨1609730054080592167864183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2146306738774122890485577 1609730054080592167864183)
              ·
                refine ⟨2414595081120888251796275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1609730054080592167864183 2414595081120888251796275)
                ·
                  refine ⟨3621892621681332377694413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2414595081120888251796275 3621892621681332377694413)
                  ·
                    refine ⟨1358209733130499641635405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3621892621681332377694413 1358209733130499641635405)
                    ·
                      refine ⟨509328649923937365613277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1358209733130499641635405 509328649923937365613277)
                      ·
                        rfl

theorem cell23_991914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_991914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_991914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_991914 prefixEnd_991914 := by exact prefixLift 991914
  have htrace : WordTrace (prefixWord ++ tailWord_991914) baseStart_991914 baseEnd_991914 := by
    simpa [prefixWord, tailWord_991914, baseEnd_991914] using wordTrace_append hprefix tailTrace_991914
  have hstable : (prefixWord ++ tailWord_991914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991914).length < 2 ^ (prefixWord ++ tailWord_991914).sum := by decide
  have hdescent : baseEnd_991914 < baseStart_991914 := by decide
  rcases family_descends (prefixWord ++ tailWord_991914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991920 : List Nat := [2, 1, 1, 1, 2, 1, 3, 2, 6, 2, 2]
def baseStart_991920 : Nat := 118140960795 + 991920 * 2 ^ 59
def prefixEnd_991920 : Nat := 4983230072969 + 3 ^ 40 * 991920 * 2
def baseEnd_991920 : Nat := 509331730807864342138249

theorem tailTrace_991920 : CollatzResearch.WordTrace tailWord_991920 prefixEnd_991920 509331730807864342138249 := by
  unfold tailWord_991920
  simp only [CollatzResearch.WordTrace]
  refine ⟨18089147283225360646986607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24118863044300480862648809 18089147283225360646986607)
  ·
    refine ⟨27133720924838040970479911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18089147283225360646986607 27133720924838040970479911)
    ·
      refine ⟨40700581387257061455719867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27133720924838040970479911 40700581387257061455719867)
      ·
        refine ⟨61050872080885592183579801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40700581387257061455719867 61050872080885592183579801)
        ·
          refine ⟨45788154060664194137684851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61050872080885592183579801 45788154060664194137684851)
          ·
            refine ⟨68682231090996291206527277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45788154060664194137684851 68682231090996291206527277)
            ·
              refine ⟨25755836659123609202447729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68682231090996291206527277 25755836659123609202447729)
              ·
                refine ⟨19316877494342706901835797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25755836659123609202447729 19316877494342706901835797)
                ·
                  refine ⟨905478632547314386023553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 19316877494342706901835797 905478632547314386023553)
                  ·
                    refine ⟨679108974410485789517665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 905478632547314386023553 679108974410485789517665)
                    ·
                      refine ⟨509331730807864342138249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 679108974410485789517665 509331730807864342138249)
                      ·
                        rfl

theorem cell23_991920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 6, 2, 2].length) (baseStart_991920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_991920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_991920 prefixEnd_991920 := by exact prefixLift 991920
  have htrace : WordTrace (prefixWord ++ tailWord_991920) baseStart_991920 baseEnd_991920 := by
    simpa [prefixWord, tailWord_991920, baseEnd_991920] using wordTrace_append hprefix tailTrace_991920
  have hstable : (prefixWord ++ tailWord_991920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991920).length < 2 ^ (prefixWord ++ tailWord_991920).sum := by decide
  have hdescent : baseEnd_991920 < baseStart_991920 := by decide
  rcases family_descends (prefixWord ++ tailWord_991920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991953 : List Nat := [1, 2, 2, 1, 2, 3, 1, 1, 4, 3, 3]
def baseStart_991953 : Nat := 118140960795 + 991953 * 2 ^ 59
def prefixEnd_991953 : Nat := 4983230072969 + 3 ^ 40 * 991953 * 2
def baseEnd_991953 : Nat := 509348675669462713025597

theorem tailTrace_991953 : CollatzResearch.WordTrace tailWord_991953 prefixEnd_991953 509348675669462713025597 := by
  unfold tailWord_991953
  simp only [CollatzResearch.WordTrace]
  refine ⟨36179498175331167929924513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24119665450220778619949675 36179498175331167929924513)
  ·
    refine ⟨27134623631498375947443385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36179498175331167929924513 27134623631498375947443385)
    ·
      refine ⟨20350967723623781960582539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27134623631498375947443385 20350967723623781960582539)
      ·
        refine ⟨30526451585435672940873809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20350967723623781960582539 30526451585435672940873809)
        ·
          refine ⟨22894838689076754705655357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30526451585435672940873809 22894838689076754705655357)
          ·
            refine ⟨8585564508403783014620759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22894838689076754705655357 8585564508403783014620759)
            ·
              refine ⟨12878346762605674521931139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8585564508403783014620759 12878346762605674521931139)
              ·
                refine ⟨19317520143908511782896709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12878346762605674521931139 19317520143908511782896709)
                ·
                  refine ⟨3622035026982845959293133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19317520143908511782896709 3622035026982845959293133)
                  ·
                    refine ⟨1358263135118567234734925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3622035026982845959293133 1358263135118567234734925)
                    ·
                      refine ⟨509348675669462713025597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1358263135118567234734925 509348675669462713025597)
                      ·
                        rfl

theorem cell23_991953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 3, 3].length) (baseStart_991953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_991953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_991953 prefixEnd_991953 := by exact prefixLift 991953
  have htrace : WordTrace (prefixWord ++ tailWord_991953) baseStart_991953 baseEnd_991953 := by
    simpa [prefixWord, tailWord_991953, baseEnd_991953] using wordTrace_append hprefix tailTrace_991953
  have hstable : (prefixWord ++ tailWord_991953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991953).length < 2 ^ (prefixWord ++ tailWord_991953).sum := by decide
  have hdescent : baseEnd_991953 < baseStart_991953 := by decide
  rcases family_descends (prefixWord ++ tailWord_991953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991954 : List Nat := [3, 2, 2, 2, 3, 1, 1, 1, 4, 2, 2]
def baseStart_991954 : Nat := 118140960795 + 991954 * 2 ^ 59
def prefixEnd_991954 : Nat := 4983230072969 + 3 ^ 40 * 991954 * 2
def baseEnd_991954 : Nat := 509349189150117209113093

theorem tailTrace_991954 : CollatzResearch.WordTrace tailWord_991954 prefixEnd_991954 509349189150117209113093 := by
  unfold tailWord_991954
  simp only [CollatzResearch.WordTrace]
  refine ⟨9044883662081886275177729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24119689765551696733807277 9044883662081886275177729)
  ·
    refine ⟨6783662746561414706383297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9044883662081886275177729 6783662746561414706383297)
    ·
      refine ⟨5087747059921061029787473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6783662746561414706383297 5087747059921061029787473)
      ·
        refine ⟨3815810294940795772340605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5087747059921061029787473 3815810294940795772340605)
        ·
          refine ⟨1430928860602798414627727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3815810294940795772340605 1430928860602798414627727)
          ·
            refine ⟨2146393290904197621941591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1430928860602798414627727 2146393290904197621941591)
            ·
              refine ⟨3219589936356296432912387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2146393290904197621941591 3219589936356296432912387)
              ·
                refine ⟨4829384904534444649368581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3219589936356296432912387 4829384904534444649368581)
                ·
                  refine ⟨905509669600208371756609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4829384904534444649368581 905509669600208371756609)
                  ·
                    refine ⟨679132252200156278817457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 905509669600208371756609 679132252200156278817457)
                    ·
                      refine ⟨509349189150117209113093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 679132252200156278817457 509349189150117209113093)
                      ·
                        rfl

theorem cell23_991954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_991954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_991954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_991954 prefixEnd_991954 := by exact prefixLift 991954
  have htrace : WordTrace (prefixWord ++ tailWord_991954) baseStart_991954 baseEnd_991954 := by
    simpa [prefixWord, tailWord_991954, baseEnd_991954] using wordTrace_append hprefix tailTrace_991954
  have hstable : (prefixWord ++ tailWord_991954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991954).length < 2 ^ (prefixWord ++ tailWord_991954).sum := by decide
  have hdescent : baseEnd_991954 < baseStart_991954 := by decide
  rcases family_descends (prefixWord ++ tailWord_991954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991960 : List Nat := [2, 1, 2, 2, 3, 2, 2, 4, 5]
def baseStart_991960 : Nat := 118140960795 + 991960 * 2 ^ 59
def prefixEnd_991960 : Nat := 4983230072969 + 3 ^ 40 * 991960 * 2
def baseEnd_991960 : Nat := 56594696670449353959785

theorem tailTrace_991960 : CollatzResearch.WordTrace tailWord_991960 prefixEnd_991960 56594696670449353959785 := by
  unfold tailWord_991960
  simp only [CollatzResearch.WordTrace]
  refine ⟨18089876743152904062714667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24119835657537205416952889 18089876743152904062714667)
  ·
    refine ⟨27134815114729356094072001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18089876743152904062714667 27134815114729356094072001)
    ·
      refine ⟨20351111336047017070554001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27134815114729356094072001 20351111336047017070554001)
      ·
        refine ⟨15263333502035262802915501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20351111336047017070554001 15263333502035262802915501)
        ·
          refine ⟨5723750063263223551093313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15263333502035262802915501 5723750063263223551093313)
          ·
            refine ⟨4292812547447417663319985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5723750063263223551093313 4292812547447417663319985)
            ·
              refine ⟨3219609410585563247489989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4292812547447417663319985 3219609410585563247489989)
              ·
                refine ⟨603676764484793108904373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3219609410585563247489989 603676764484793108904373)
                ·
                  refine ⟨56594696670449353959785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 603676764484793108904373 56594696670449353959785)
                  ·
                    rfl

theorem cell23_991960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 4, 5].length) (baseStart_991960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_991960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_991960 prefixEnd_991960 := by exact prefixLift 991960
  have htrace : WordTrace (prefixWord ++ tailWord_991960) baseStart_991960 baseEnd_991960 := by
    simpa [prefixWord, tailWord_991960, baseEnd_991960] using wordTrace_append hprefix tailTrace_991960
  have hstable : (prefixWord ++ tailWord_991960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991960).length < 2 ^ (prefixWord ++ tailWord_991960).sum := by decide
  have hdescent : baseEnd_991960 < baseStart_991960 := by decide
  rcases family_descends (prefixWord ++ tailWord_991960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991971 : List Nat := [1, 1, 1, 7, 1, 2, 3, 1, 2, 2, 2]
def baseStart_991971 : Nat := 118140960795 + 991971 * 2 ^ 59
def prefixEnd_991971 : Nat := 4983230072969 + 3 ^ 40 * 991971 * 2
def baseEnd_991971 : Nat := 509357918321243642600515

theorem tailTrace_991971 : CollatzResearch.WordTrace tailWord_991971 prefixEnd_991971 509357918321243642600515 := by
  unfold tailWord_991971
  simp only [CollatzResearch.WordTrace]
  refine ⟨36180154689265957004079767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24120103126177304669386511 36180154689265957004079767)
  ·
    refine ⟨54270232033898935506119651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36180154689265957004079767 54270232033898935506119651)
    ·
      refine ⟨81405348050848403259179477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54270232033898935506119651 81405348050848403259179477)
      ·
        refine ⟨1907937844941759451387019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 81405348050848403259179477 1907937844941759451387019)
        ·
          refine ⟨2861906767412639177080529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1907937844941759451387019 2861906767412639177080529)
          ·
            refine ⟨2146430075559479382810397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2861906767412639177080529 2146430075559479382810397)
            ·
              refine ⟨804911278334804768553899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2146430075559479382810397 804911278334804768553899)
              ·
                refine ⟨1207366917502207152830849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 804911278334804768553899 1207366917502207152830849)
                ·
                  refine ⟨905525188126655364623137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1207366917502207152830849 905525188126655364623137)
                  ·
                    refine ⟨679143891094991523467353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 905525188126655364623137 679143891094991523467353)
                    ·
                      refine ⟨509357918321243642600515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 679143891094991523467353 509357918321243642600515)
                      ·
                        rfl

theorem cell23_991971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_991971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_991971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_991971 prefixEnd_991971 := by exact prefixLift 991971
  have htrace : WordTrace (prefixWord ++ tailWord_991971) baseStart_991971 baseEnd_991971 := by
    simpa [prefixWord, tailWord_991971, baseEnd_991971] using wordTrace_append hprefix tailTrace_991971
  have hstable : (prefixWord ++ tailWord_991971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991971).length < 2 ^ (prefixWord ++ tailWord_991971).sum := by decide
  have hdescent : baseEnd_991971 < baseStart_991971 := by decide
  rcases family_descends (prefixWord ++ tailWord_991971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991973 : List Nat := [1, 3, 1, 4, 1, 2, 1, 2, 1, 7]
def baseStart_991973 : Nat := 118140960795 + 991973 * 2 ^ 59
def prefixEnd_991973 : Nat := 4983230072969 + 3 ^ 40 * 991973 * 2
def baseEnd_991973 : Nat := 169786315094184211591835

theorem tailTrace_991973 : CollatzResearch.WordTrace tailWord_991973 prefixEnd_991973 169786315094184211591835 := by
  unfold tailWord_991973
  simp only [CollatzResearch.WordTrace]
  refine ⟨36180227635258711345652573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24120151756839140897101715 36180227635258711345652573)
  ·
    refine ⟨13567585363222016754619715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36180227635258711345652573 13567585363222016754619715)
    ·
      refine ⟨20351378044833025131929573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13567585363222016754619715 20351378044833025131929573)
      ·
        refine ⟨3815883383406192212236795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20351378044833025131929573 3815883383406192212236795)
        ·
          refine ⟨5723825075109288318355193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3815883383406192212236795 5723825075109288318355193)
          ·
            refine ⟨4292868806331966238766395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5723825075109288318355193 4292868806331966238766395)
            ·
              refine ⟨6439303209497949358149593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4292868806331966238766395 6439303209497949358149593)
              ·
                refine ⟨4829477407123462018612195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6439303209497949358149593 4829477407123462018612195)
                ·
                  refine ⟨7244216110685193027918293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4829477407123462018612195 7244216110685193027918293)
                  ·
                    refine ⟨169786315094184211591835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7244216110685193027918293 169786315094184211591835)
                    ·
                      rfl

theorem cell23_991973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 7].length) (baseStart_991973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_991973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_991973 prefixEnd_991973 := by exact prefixLift 991973
  have htrace : WordTrace (prefixWord ++ tailWord_991973) baseStart_991973 baseEnd_991973 := by
    simpa [prefixWord, tailWord_991973, baseEnd_991973] using wordTrace_append hprefix tailTrace_991973
  have hstable : (prefixWord ++ tailWord_991973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991973).length < 2 ^ (prefixWord ++ tailWord_991973).sum := by decide
  have hdescent : baseEnd_991973 < baseStart_991973 := by decide
  rcases family_descends (prefixWord ++ tailWord_991973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991990 : List Nat := [5, 1, 1, 1, 1, 2, 2, 3, 2, 5]
def baseStart_991990 : Nat := 118140960795 + 991990 * 2 ^ 59
def prefixEnd_991990 : Nat := 4983230072969 + 3 ^ 40 * 991990 * 2
def baseEnd_991990 : Nat := 169789224817893022754309

theorem tailTrace_991990 : CollatzResearch.WordTrace tailWord_991990 prefixEnd_991990 169789224817893022754309 := by
  unfold tailWord_991990
  simp only [CollatzResearch.WordTrace]
  refine ⟨2261302979762320203063839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24120565117464748832680949 2261302979762320203063839)
  ·
    refine ⟨3391954469643480304595759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2261302979762320203063839 3391954469643480304595759)
    ·
      refine ⟨5087931704465220456893639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3391954469643480304595759 5087931704465220456893639)
      ·
        refine ⟨7631897556697830685340459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5087931704465220456893639 7631897556697830685340459)
        ·
          refine ⟨11447846335046746028010689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7631897556697830685340459 11447846335046746028010689)
          ·
            refine ⟨8585884751285059521008017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11447846335046746028010689 8585884751285059521008017)
            ·
              refine ⟨6439413563463794640756013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8585884751285059521008017 6439413563463794640756013)
              ·
                refine ⟨2414780086298922990283505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6439413563463794640756013 2414780086298922990283505)
                ·
                  refine ⟨1811085064724192242712629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2414780086298922990283505 1811085064724192242712629)
                  ·
                    refine ⟨169789224817893022754309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1811085064724192242712629 169789224817893022754309)
                    ·
                      rfl

theorem cell23_991990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_991990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_991990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_991990 prefixEnd_991990 := by exact prefixLift 991990
  have htrace : WordTrace (prefixWord ++ tailWord_991990) baseStart_991990 baseEnd_991990 := by
    simpa [prefixWord, tailWord_991990, baseEnd_991990] using wordTrace_append hprefix tailTrace_991990
  have hstable : (prefixWord ++ tailWord_991990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991990).length < 2 ^ (prefixWord ++ tailWord_991990).sum := by decide
  have hdescent : baseEnd_991990 < baseStart_991990 := by decide
  rcases family_descends (prefixWord ++ tailWord_991990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991993 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 6, 1, 4]
def baseStart_991993 : Nat := 118140960795 + 991993 * 2 ^ 59
def prefixEnd_991993 : Nat := 4983230072969 + 3 ^ 40 * 991993 * 2
def baseEnd_991993 : Nat := 509369214895642556525413

theorem tailTrace_991993 : CollatzResearch.WordTrace tailWord_991993 prefixEnd_991993 509369214895642556525413 := by
  unfold tailWord_991993
  simp only [CollatzResearch.WordTrace]
  refine ⟨36180957095186254761380633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24120638063457503174253755 36180957095186254761380633)
  ·
    refine ⟨27135717821389691071035475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36180957095186254761380633 27135717821389691071035475)
    ·
      refine ⟨40703576732084536606553213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27135717821389691071035475 40703576732084536606553213)
      ·
        refine ⟨15263841274531701227457455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40703576732084536606553213 15263841274531701227457455)
        ·
          refine ⟨22895761911797551841186183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15263841274531701227457455 22895761911797551841186183)
          ·
            refine ⟨34343642867696327761779275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22895761911797551841186183 34343642867696327761779275)
            ·
              refine ⟨51515464301544491642668913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34343642867696327761779275 51515464301544491642668913)
              ·
                refine ⟨38636598226158368732001685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51515464301544491642668913 38636598226158368732001685)
                ·
                  refine ⟨1811090541851173534312579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 38636598226158368732001685 1811090541851173534312579)
                  ·
                    refine ⟨2716635812776760301468869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1811090541851173534312579 2716635812776760301468869)
                    ·
                      refine ⟨509369214895642556525413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2716635812776760301468869 509369214895642556525413)
                      ·
                        rfl

theorem cell23_991993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_991993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_991993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_991993 prefixEnd_991993 := by exact prefixLift 991993
  have htrace : WordTrace (prefixWord ++ tailWord_991993) baseStart_991993 baseEnd_991993 := by
    simpa [prefixWord, tailWord_991993, baseEnd_991993] using wordTrace_append hprefix tailTrace_991993
  have hstable : (prefixWord ++ tailWord_991993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991993).length < 2 ^ (prefixWord ++ tailWord_991993).sum := by decide
  have hdescent : baseEnd_991993 < baseStart_991993 := by decide
  rcases family_descends (prefixWord ++ tailWord_991993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992010 : List Nat := [3, 1, 2, 2, 1, 2, 3, 2, 2, 1, 4]
def baseStart_992010 : Nat := 118140960795 + 992010 * 2 ^ 59
def prefixEnd_992010 : Nat := 4983230072969 + 3 ^ 40 * 992010 * 2
def baseEnd_992010 : Nat := 509377944066768990012835

theorem tailTrace_992010 : CollatzResearch.WordTrace tailWord_992010 prefixEnd_992010 509377944066768990012835 := by
  unfold tailWord_992010
  simp only [CollatzResearch.WordTrace]
  refine ⟨9045394284031166666187371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24121051424083111109832989 9045394284031166666187371)
  ·
    refine ⟨13568091426046749999281057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9045394284031166666187371 13568091426046749999281057)
    ·
      refine ⟨10176068569535062499460793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13568091426046749999281057 10176068569535062499460793)
      ·
        refine ⟨7632051427151296874595595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10176068569535062499460793 7632051427151296874595595)
        ·
          refine ⟨11448077140726945311893393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7632051427151296874595595 11448077140726945311893393)
          ·
            refine ⟨8586057855545208983920045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11448077140726945311893393 8586057855545208983920045)
            ·
              refine ⟨3219771695829453368970017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8586057855545208983920045 3219771695829453368970017)
              ·
                refine ⟨2414828771872090026727513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3219771695829453368970017 2414828771872090026727513)
                ·
                  refine ⟨1811121578904067520045635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2414828771872090026727513 1811121578904067520045635)
                  ·
                    refine ⟨2716682368356101280068453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1811121578904067520045635 2716682368356101280068453)
                    ·
                      refine ⟨509377944066768990012835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2716682368356101280068453 509377944066768990012835)
                      ·
                        rfl

theorem cell23_992010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_992010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_992010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_992010 prefixEnd_992010 := by exact prefixLift 992010
  have htrace : WordTrace (prefixWord ++ tailWord_992010) baseStart_992010 baseEnd_992010 := by
    simpa [prefixWord, tailWord_992010, baseEnd_992010] using wordTrace_append hprefix tailTrace_992010
  have hstable : (prefixWord ++ tailWord_992010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992010).length < 2 ^ (prefixWord ++ tailWord_992010).sum := by decide
  have hdescent : baseEnd_992010 < baseStart_992010 := by decide
  rcases family_descends (prefixWord ++ tailWord_992010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992043 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 1, 7, 3]
def baseStart_992043 : Nat := 118140960795 + 992043 * 2 ^ 59
def prefixEnd_992043 : Nat := 4983230072969 + 3 ^ 40 * 992043 * 2
def baseEnd_992043 : Nat := 509394888928367360900183

theorem tailTrace_992043 : CollatzResearch.WordTrace tailWord_992043 prefixEnd_992043 509394888928367360900183 := by
  unfold tailWord_992043
  simp only [CollatzResearch.WordTrace]
  refine ⟨36182780745005113300700783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24121853830003408867133855 36182780745005113300700783)
  ·
    refine ⟨54274171117507669951051175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36182780745005113300700783 54274171117507669951051175)
    ·
      refine ⟨81411256676261504926576763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54274171117507669951051175 81411256676261504926576763)
      ·
        refine ⟨122116885014392257389865145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81411256676261504926576763 122116885014392257389865145)
        ·
          refine ⟨91587663760794193042398859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122116885014392257389865145 91587663760794193042398859)
          ·
            refine ⟨137381495641191289563598289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91587663760794193042398859 137381495641191289563598289)
            ·
              refine ⟨103036121730893467172698717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137381495641191289563598289 103036121730893467172698717)
              ·
                refine ⟨38638545649085050189762019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103036121730893467172698717 38638545649085050189762019)
                ·
                  refine ⟨57957818473627575284643029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38638545649085050189762019 57957818473627575284643029)
                  ·
                    refine ⟨1358386370475646295733821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57957818473627575284643029 1358386370475646295733821)
                    ·
                      refine ⟨509394888928367360900183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1358386370475646295733821 509394888928367360900183)
                      ·
                        rfl

theorem cell23_992043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 7, 3].length) (baseStart_992043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_992043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_992043 prefixEnd_992043 := by exact prefixLift 992043
  have htrace : WordTrace (prefixWord ++ tailWord_992043) baseStart_992043 baseEnd_992043 := by
    simpa [prefixWord, tailWord_992043, baseEnd_992043] using wordTrace_append hprefix tailTrace_992043
  have hstable : (prefixWord ++ tailWord_992043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992043).length < 2 ^ (prefixWord ++ tailWord_992043).sum := by decide
  have hdescent : baseEnd_992043 < baseStart_992043 := by decide
  rcases family_descends (prefixWord ++ tailWord_992043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992104 : List Nat := [2, 1, 4, 2, 1, 2, 3, 1, 2, 3, 2]
def baseStart_992104 : Nat := 118140960795 + 992104 * 2 ^ 59
def prefixEnd_992104 : Nat := 4983230072969 + 3 ^ 40 * 992104 * 2
def baseEnd_992104 : Nat := 509426211248291622237403

theorem tailTrace_992104 : CollatzResearch.WordTrace tailWord_992104 prefixEnd_992104 509426211248291622237403 := by
  unfold tailWord_992104
  simp only [CollatzResearch.WordTrace]
  refine ⟨18092502798892060359335683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24123337065189413812447577 18092502798892060359335683)
  ·
    refine ⟨27138754198338090539003525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18092502798892060359335683 27138754198338090539003525)
    ·
      refine ⟨5088516412188391976063161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27138754198338090539003525 5088516412188391976063161)
      ·
        refine ⟨3816387309141293982047371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5088516412188391976063161 3816387309141293982047371)
        ·
          refine ⟨5724580963711940973071057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3816387309141293982047371 5724580963711940973071057)
          ·
            refine ⟨4293435722783955729803293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5724580963711940973071057 4293435722783955729803293)
            ·
              refine ⟨1610038396043983398676235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4293435722783955729803293 1610038396043983398676235)
              ·
                refine ⟨2415057594065975098014353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1610038396043983398676235 2415057594065975098014353)
                ·
                  refine ⟨1811293195549481323510765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2415057594065975098014353 1811293195549481323510765)
                  ·
                    refine ⟨679234948331055496316537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1811293195549481323510765 679234948331055496316537)
                    ·
                      refine ⟨509426211248291622237403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 679234948331055496316537 509426211248291622237403)
                      ·
                        rfl

theorem cell23_992104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_992104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_992104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_992104 prefixEnd_992104 := by exact prefixLift 992104
  have htrace : WordTrace (prefixWord ++ tailWord_992104) baseStart_992104 baseEnd_992104 := by
    simpa [prefixWord, tailWord_992104, baseEnd_992104] using wordTrace_append hprefix tailTrace_992104
  have hstable : (prefixWord ++ tailWord_992104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992104).length < 2 ^ (prefixWord ++ tailWord_992104).sum := by decide
  have hdescent : baseEnd_992104 < baseStart_992104 := by decide
  rcases family_descends (prefixWord ++ tailWord_992104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992120 : List Nat := [2, 1, 2, 1, 1, 1, 1, 4, 5, 2, 3]
def baseStart_992120 : Nat := 118140960795 + 992120 * 2 ^ 59
def prefixEnd_992120 : Nat := 4983230072969 + 3 ^ 40 * 992120 * 2
def baseEnd_992120 : Nat := 509434426938763559637329

theorem tailTrace_992120 : CollatzResearch.WordTrace tailWord_992120 prefixEnd_992120 509434426938763559637329 := by
  unfold tailWord_992120
  simp only [CollatzResearch.WordTrace]
  refine ⟨18092794582863077725626907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24123726110484103634169209 18092794582863077725626907)
  ·
    refine ⟨27139191874294616588440361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18092794582863077725626907 27139191874294616588440361)
    ·
      refine ⟨20354393905720962441330271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27139191874294616588440361 20354393905720962441330271)
      ·
        refine ⟨30531590858581443661995407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20354393905720962441330271 30531590858581443661995407)
        ·
          refine ⟨45797386287872165492993111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30531590858581443661995407 45797386287872165492993111)
          ·
            refine ⟨68696079431808248239489667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45797386287872165492993111 68696079431808248239489667)
            ·
              refine ⟨103044119147712372359234501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68696079431808248239489667 103044119147712372359234501)
              ·
                refine ⟨19320772340196069817356469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103044119147712372359234501 19320772340196069817356469)
                ·
                  refine ⟨1811322406893381545377169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19320772340196069817356469 1811322406893381545377169)
                  ·
                    refine ⟨1358491805170036159032877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1811322406893381545377169 1358491805170036159032877)
                    ·
                      refine ⟨509434426938763559637329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1358491805170036159032877 509434426938763559637329)
                      ·
                        rfl

theorem cell23_992120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 5, 2, 3].length) (baseStart_992120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_992120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_992120 prefixEnd_992120 := by exact prefixLift 992120
  have htrace : WordTrace (prefixWord ++ tailWord_992120) baseStart_992120 baseEnd_992120 := by
    simpa [prefixWord, tailWord_992120, baseEnd_992120] using wordTrace_append hprefix tailTrace_992120
  have hstable : (prefixWord ++ tailWord_992120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992120).length < 2 ^ (prefixWord ++ tailWord_992120).sum := by decide
  have hdescent : baseEnd_992120 < baseStart_992120 := by decide
  rcases family_descends (prefixWord ++ tailWord_992120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992127 : List Nat := [1, 1, 2, 2, 1, 1, 7, 2, 2, 4]
def baseStart_992127 : Nat := 118140960795 + 992127 * 2 ^ 59
def prefixEnd_992127 : Nat := 4983230072969 + 3 ^ 40 * 992127 * 2
def baseEnd_992127 : Nat := 169812673767781677416599

theorem tailTrace_992127 : CollatzResearch.WordTrace tailWord_992127 prefixEnd_992127 169812673767781677416599 := by
  unfold tailWord_992127
  simp only [CollatzResearch.WordTrace]
  refine ⟨36185844476700795646758635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24123896317800530431172423 36185844476700795646758635)
  ·
    refine ⟨54278766715051193470137953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36185844476700795646758635 54278766715051193470137953)
    ·
      refine ⟨40709075036288395102603465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54278766715051193470137953 40709075036288395102603465)
      ·
        refine ⟨30531806277216296326952599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40709075036288395102603465 30531806277216296326952599)
        ·
          refine ⟨45797709415824444490428899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30531806277216296326952599 45797709415824444490428899)
          ·
            refine ⟨68696564123736666735643349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45797709415824444490428899 68696564123736666735643349)
            ·
              refine ⟨1610075721650078126616641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 68696564123736666735643349 1610075721650078126616641)
              ·
                refine ⟨1207556791237558594962481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1610075721650078126616641 1207556791237558594962481)
                ·
                  refine ⟨905667593428168946221861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1207556791237558594962481 905667593428168946221861)
                  ·
                    refine ⟨169812673767781677416599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 905667593428168946221861 169812673767781677416599)
                    ·
                      rfl

theorem cell23_992127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 2, 2, 4].length) (baseStart_992127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_992127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_992127 prefixEnd_992127 := by exact prefixLift 992127
  have htrace : WordTrace (prefixWord ++ tailWord_992127) baseStart_992127 baseEnd_992127 := by
    simpa [prefixWord, tailWord_992127, baseEnd_992127] using wordTrace_append hprefix tailTrace_992127
  have hstable : (prefixWord ++ tailWord_992127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992127).length < 2 ^ (prefixWord ++ tailWord_992127).sum := by decide
  have hdescent : baseEnd_992127 < baseStart_992127 := by decide
  rcases family_descends (prefixWord ++ tailWord_992127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992241 : List Nat := [1, 2, 2, 2, 4, 1, 1, 4, 2, 2, 2]
def baseStart_992241 : Nat := 118140960795 + 992241 * 2 ^ 59
def prefixEnd_992241 : Nat := 4983230072969 + 3 ^ 40 * 992241 * 2
def baseEnd_992241 : Nat := 509496558097957586224273

theorem tailTrace_992241 : CollatzResearch.WordTrace tailWord_992241 prefixEnd_992241 509496558097957586224273 := by
  unfold tailWord_992241
  simp only [CollatzResearch.WordTrace]
  refine ⟨36190002398287793116408577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24126668265525195410939051 36190002398287793116408577)
  ·
    refine ⟨27142501798715844837306433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36190002398287793116408577 27142501798715844837306433)
    ·
      refine ⟨20356876349036883627979825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27142501798715844837306433 20356876349036883627979825)
      ·
        refine ⟨15267657261777662720984869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20356876349036883627979825 15267657261777662720984869)
        ·
          refine ⟨2862685736583311760184663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15267657261777662720984869 2862685736583311760184663)
          ·
            refine ⟨4294028604874967640276995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2862685736583311760184663 4294028604874967640276995)
            ·
              refine ⟨6441042907312451460415493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4294028604874967640276995 6441042907312451460415493)
              ·
                refine ⟨1207695545121084648827905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6441042907312451460415493 1207695545121084648827905)
                ·
                  refine ⟨905771658840813486620929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1207695545121084648827905 905771658840813486620929)
                  ·
                    refine ⟨679328744130610114965697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 905771658840813486620929 679328744130610114965697)
                    ·
                      refine ⟨509496558097957586224273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 679328744130610114965697 509496558097957586224273)
                      ·
                        rfl

theorem cell23_992241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 4, 2, 2, 2].length) (baseStart_992241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_992241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_992241 prefixEnd_992241 := by exact prefixLift 992241
  have htrace : WordTrace (prefixWord ++ tailWord_992241) baseStart_992241 baseEnd_992241 := by
    simpa [prefixWord, tailWord_992241, baseEnd_992241] using wordTrace_append hprefix tailTrace_992241
  have hstable : (prefixWord ++ tailWord_992241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992241).length < 2 ^ (prefixWord ++ tailWord_992241).sum := by decide
  have hdescent : baseEnd_992241 < baseStart_992241 := by decide
  rcases family_descends (prefixWord ++ tailWord_992241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992257 : List Nat := [1, 2, 4, 1, 2, 2, 1, 1, 1, 5, 3]
def baseStart_992257 : Nat := 118140960795 + 992257 * 2 ^ 59
def prefixEnd_992257 : Nat := 4983230072969 + 3 ^ 40 * 992257 * 2
def baseEnd_992257 : Nat := 509504773788429523624199

theorem tailTrace_992257 : CollatzResearch.WordTrace tailWord_992257 prefixEnd_992257 509504773788429523624199 := by
  unfold tailWord_992257
  simp only [CollatzResearch.WordTrace]
  refine ⟨36190585966229827848991025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24127057310819885232660683 36190585966229827848991025)
  ·
    refine ⟨27142939474672370886743269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36190585966229827848991025 27142939474672370886743269)
    ·
      refine ⟨5089301151501069541264363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27142939474672370886743269 5089301151501069541264363)
      ·
        refine ⟨7633951727251604311896545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5089301151501069541264363 7633951727251604311896545)
        ·
          refine ⟨5725463795438703233922409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7633951727251604311896545 5725463795438703233922409)
          ·
            refine ⟨4294097846579027425441807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5725463795438703233922409 4294097846579027425441807)
            ·
              refine ⟨6441146769868541138162711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4294097846579027425441807 6441146769868541138162711)
              ·
                refine ⟨9661720154802811707244067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6441146769868541138162711 9661720154802811707244067)
                ·
                  refine ⟨14492580232204217560866101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9661720154802811707244067 14492580232204217560866101)
                  ·
                    refine ⟨1358679396769145396331197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14492580232204217560866101 1358679396769145396331197)
                    ·
                      refine ⟨509504773788429523624199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1358679396769145396331197 509504773788429523624199)
                      ·
                        rfl

theorem cell23_992257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_992257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_992257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_992257 prefixEnd_992257 := by exact prefixLift 992257
  have htrace : WordTrace (prefixWord ++ tailWord_992257) baseStart_992257 baseEnd_992257 := by
    simpa [prefixWord, tailWord_992257, baseEnd_992257] using wordTrace_append hprefix tailTrace_992257
  have hstable : (prefixWord ++ tailWord_992257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992257).length < 2 ^ (prefixWord ++ tailWord_992257).sum := by decide
  have hdescent : baseEnd_992257 < baseStart_992257 := by decide
  rcases family_descends (prefixWord ++ tailWord_992257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992277 : List Nat := [1, 3, 2, 1, 4, 2, 1, 1, 1, 7]
def baseStart_992277 : Nat := 118140960795 + 992277 * 2 ^ 59
def prefixEnd_992277 : Nat := 4983230072969 + 3 ^ 40 * 992277 * 2
def baseEnd_992277 : Nat := 169838347800506481791369

theorem tailTrace_992277 : CollatzResearch.WordTrace tailWord_992277 prefixEnd_992277 169838347800506481791369 := by
  unfold tailWord_992277
  simp only [CollatzResearch.WordTrace]
  refine ⟨36191315426157371264719085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24127543617438247509812723 36191315426157371264719085)
  ·
    refine ⟨13571743284809014224269657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36191315426157371264719085 13571743284809014224269657)
    ·
      refine ⟨10178807463606760668202243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13571743284809014224269657 10178807463606760668202243)
      ·
        refine ⟨15268211195410141002303365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10178807463606760668202243 15268211195410141002303365)
        ·
          refine ⟨2862789599139401437931881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15268211195410141002303365 2862789599139401437931881)
          ·
            refine ⟨2147092199354551078448911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2862789599139401437931881 2147092199354551078448911)
            ·
              refine ⟨3220638299031826617673367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2147092199354551078448911 3220638299031826617673367)
              ·
                refine ⟨4830957448547739926510051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3220638299031826617673367 4830957448547739926510051)
                ·
                  refine ⟨7246436172821609889765077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4830957448547739926510051 7246436172821609889765077)
                  ·
                    refine ⟨169838347800506481791369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7246436172821609889765077 169838347800506481791369)
                    ·
                      rfl

theorem cell23_992277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 7].length) (baseStart_992277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_992277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_992277 prefixEnd_992277 := by exact prefixLift 992277
  have htrace : WordTrace (prefixWord ++ tailWord_992277) baseStart_992277 baseEnd_992277 := by
    simpa [prefixWord, tailWord_992277, baseEnd_992277] using wordTrace_append hprefix tailTrace_992277
  have hstable : (prefixWord ++ tailWord_992277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992277).length < 2 ^ (prefixWord ++ tailWord_992277).sum := by decide
  have hdescent : baseEnd_992277 < baseStart_992277 := by decide
  rcases family_descends (prefixWord ++ tailWord_992277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992297 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 2, 10, 2]
def baseStart_992297 : Nat := 118140960795 + 992297 * 2 ^ 59
def prefixEnd_992297 : Nat := 4983230072969 + 3 ^ 40 * 992297 * 2
def baseEnd_992297 : Nat := 509525313014609367124015

theorem tailTrace_992297 : CollatzResearch.WordTrace tailWord_992297 prefixEnd_992297 509525313014609367124015 := by
  unfold tailWord_992297
  simp only [CollatzResearch.WordTrace]
  refine ⟨36192044886084914680447145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24128029924056609786964763 36192044886084914680447145)
  ·
    refine ⟨27144033664563686010335359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36192044886084914680447145 27144033664563686010335359)
    ·
      refine ⟨40716050496845529015503039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27144033664563686010335359 40716050496845529015503039)
      ·
        refine ⟨61074075745268293523254559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40716050496845529015503039 61074075745268293523254559)
        ·
          refine ⟨91611113617902440284881839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61074075745268293523254559 91611113617902440284881839)
          ·
            refine ⟨137416670426853660427322759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91611113617902440284881839 137416670426853660427322759)
            ·
              refine ⟨206125005640280490640984139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137416670426853660427322759 206125005640280490640984139)
              ·
                refine ⟨309187508460420735961476209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206125005640280490640984139 309187508460420735961476209)
                ·
                  refine ⟨231890631345315551971107157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 309187508460420735961476209 231890631345315551971107157)
                  ·
                    refine ⟨679367084019479156165353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 231890631345315551971107157 679367084019479156165353)
                    ·
                      refine ⟨509525313014609367124015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 679367084019479156165353 509525313014609367124015)
                      ·
                        rfl

theorem cell23_992297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 10, 2].length) (baseStart_992297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_992297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_992297 prefixEnd_992297 := by exact prefixLift 992297
  have htrace : WordTrace (prefixWord ++ tailWord_992297) baseStart_992297 baseEnd_992297 := by
    simpa [prefixWord, tailWord_992297, baseEnd_992297] using wordTrace_append hprefix tailTrace_992297
  have hstable : (prefixWord ++ tailWord_992297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992297).length < 2 ^ (prefixWord ++ tailWord_992297).sum := by decide
  have hdescent : baseEnd_992297 < baseStart_992297 := by decide
  rcases family_descends (prefixWord ++ tailWord_992297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992314 : List Nat := [3, 1, 1, 1, 3, 1, 4, 1, 2, 4, 2]
def baseStart_992314 : Nat := 118140960795 + 992314 * 2 ^ 59
def prefixEnd_992314 : Nat := 4983230072969 + 3 ^ 40 * 992314 * 2
def baseEnd_992314 : Nat := 509534042185735800611437

theorem tailTrace_992314 : CollatzResearch.WordTrace tailWord_992314 prefixEnd_992314 509534042185735800611437 := by
  unfold tailWord_992314
  simp only [CollatzResearch.WordTrace]
  refine ⟨9048166231755831645953999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24128443284682217722543997 9048166231755831645953999)
  ·
    refine ⟨13572249347633747468930999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9048166231755831645953999 13572249347633747468930999)
    ·
      refine ⟨20358374021450621203396499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13572249347633747468930999 20358374021450621203396499)
      ·
        refine ⟨30537561032175931805094749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20358374021450621203396499 30537561032175931805094749)
        ·
          refine ⟨11451585387065974426910531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30537561032175931805094749 11451585387065974426910531)
          ·
            refine ⟨17177378080598961640365797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11451585387065974426910531 17177378080598961640365797)
            ·
              refine ⟨3220758390112305307568587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17177378080598961640365797 3220758390112305307568587)
              ·
                refine ⟨4831137585168457961352881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3220758390112305307568587 4831137585168457961352881)
                ·
                  refine ⟨3623353188876343471014661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4831137585168457961352881 3623353188876343471014661)
                  ·
                    refine ⟨679378722914314400815249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3623353188876343471014661 679378722914314400815249)
                    ·
                      refine ⟨509534042185735800611437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 679378722914314400815249 509534042185735800611437)
                      ·
                        rfl

theorem cell23_992314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 2, 4, 2].length) (baseStart_992314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_992314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_992314 prefixEnd_992314 := by exact prefixLift 992314
  have htrace : WordTrace (prefixWord ++ tailWord_992314) baseStart_992314 baseEnd_992314 := by
    simpa [prefixWord, tailWord_992314, baseEnd_992314] using wordTrace_append hprefix tailTrace_992314
  have hstable : (prefixWord ++ tailWord_992314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992314).length < 2 ^ (prefixWord ++ tailWord_992314).sum := by decide
  have hdescent : baseEnd_992314 < baseStart_992314 := by decide
  rcases family_descends (prefixWord ++ tailWord_992314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992334 : List Nat := [4, 1, 1, 1, 1, 3, 2, 3, 2, 2, 3]
def baseStart_992334 : Nat := 118140960795 + 992334 * 2 ^ 59
def prefixEnd_992334 : Nat := 4983230072969 + 3 ^ 40 * 992334 * 2
def baseEnd_992334 : Nat := 509544311798825722361345

theorem tailTrace_992334 : CollatzResearch.WordTrace tailWord_992334 prefixEnd_992334 509544311798825722361345 := by
  unfold tailWord_992334
  simp only [CollatzResearch.WordTrace]
  refine ⟨4524174298368858749943007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24128929591300579999696037 4524174298368858749943007)
  ·
    refine ⟨6786261447553288124914511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4524174298368858749943007 6786261447553288124914511)
    ·
      refine ⟨10179392171329932187371767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6786261447553288124914511 10179392171329932187371767)
      ·
        refine ⟨15269088256994898281057651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10179392171329932187371767 15269088256994898281057651)
        ·
          refine ⟨22903632385492347421586477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15269088256994898281057651 22903632385492347421586477)
          ·
            refine ⟨8588862144559630283094929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22903632385492347421586477 8588862144559630283094929)
            ·
              refine ⟨6441646608419722712321197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8588862144559630283094929 6441646608419722712321197)
              ·
                refine ⟨2415617478157396017120449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6441646608419722712321197 2415617478157396017120449)
                ·
                  refine ⟨1811713108618047012840337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2415617478157396017120449 1811713108618047012840337)
                  ·
                    refine ⟨1358784831463535259630253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1811713108618047012840337 1358784831463535259630253)
                    ·
                      refine ⟨509544311798825722361345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1358784831463535259630253 509544311798825722361345)
                      ·
                        rfl

theorem cell23_992334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 2, 2, 3].length) (baseStart_992334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_992334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_992334 prefixEnd_992334 := by exact prefixLift 992334
  have htrace : WordTrace (prefixWord ++ tailWord_992334) baseStart_992334 baseEnd_992334 := by
    simpa [prefixWord, tailWord_992334, baseEnd_992334] using wordTrace_append hprefix tailTrace_992334
  have hstable : (prefixWord ++ tailWord_992334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992334).length < 2 ^ (prefixWord ++ tailWord_992334).sum := by decide
  have hdescent : baseEnd_992334 < baseStart_992334 := by decide
  rcases family_descends (prefixWord ++ tailWord_992334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992354 : List Nat := [3, 3, 2, 2, 1, 1, 2, 1, 8]
def baseStart_992354 : Nat := 118140960795 + 992354 * 2 ^ 59
def prefixEnd_992354 : Nat := 4983230072969 + 3 ^ 40 * 992354 * 2
def baseEnd_992354 : Nat := 56617175712435071567917

theorem tailTrace_992354 : CollatzResearch.WordTrace tailWord_992354 prefixEnd_992354 56617175712435071567917 := by
  unfold tailWord_992354
  simp only [CollatzResearch.WordTrace]
  refine ⟨9048530961719603353818029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24129415897918942276848077 9048530961719603353818029)
  ·
    refine ⟨3393199110644851257681761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9048530961719603353818029 3393199110644851257681761)
    ·
      refine ⟨2544899332983638443261321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3393199110644851257681761 2544899332983638443261321)
      ·
        refine ⟨1908674499737728832445991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2544899332983638443261321 1908674499737728832445991)
        ·
          refine ⟨2863011749606593248668987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1908674499737728832445991 2863011749606593248668987)
          ·
            refine ⟨4294517624409889873003481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2863011749606593248668987 4294517624409889873003481)
            ·
              refine ⟨3220888218307417404752611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4294517624409889873003481 3220888218307417404752611)
              ·
                refine ⟨4831332327461126107128917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3220888218307417404752611 4831332327461126107128917)
                ·
                  refine ⟨56617175712435071567917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4831332327461126107128917 56617175712435071567917)
                  ·
                    rfl

theorem cell23_992354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 8].length) (baseStart_992354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_992354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_992354 prefixEnd_992354 := by exact prefixLift 992354
  have htrace : WordTrace (prefixWord ++ tailWord_992354) baseStart_992354 baseEnd_992354 := by
    simpa [prefixWord, tailWord_992354, baseEnd_992354] using wordTrace_append hprefix tailTrace_992354
  have hstable : (prefixWord ++ tailWord_992354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992354).length < 2 ^ (prefixWord ++ tailWord_992354).sum := by decide
  have hdescent : baseEnd_992354 < baseStart_992354 := by decide
  rcases family_descends (prefixWord ++ tailWord_992354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992367 : List Nat := [1, 1, 2, 1, 3, 3, 2, 2, 3, 5]
def baseStart_992367 : Nat := 118140960795 + 992367 * 2 ^ 59
def prefixEnd_992367 : Nat := 4983230072969 + 3 ^ 40 * 992367 * 2
def baseEnd_992367 : Nat := 169853752220141364416231

theorem tailTrace_992367 : CollatzResearch.WordTrace tailWord_992367 prefixEnd_992367 169853752220141364416231 := by
  unfold tailWord_992367
  simp only [CollatzResearch.WordTrace]
  refine ⟨36194597995831316635495355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24129731997220877756996903 36194597995831316635495355)
  ·
    refine ⟨54291896993746974953243033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36194597995831316635495355 54291896993746974953243033)
    ·
      refine ⟨40718922745310231214932275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54291896993746974953243033 40718922745310231214932275)
      ·
        refine ⟨61078384117965346822398413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40718922745310231214932275 61078384117965346822398413)
        ·
          refine ⟨22904394044237005058399405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61078384117965346822398413 22904394044237005058399405)
          ·
            refine ⟨8589147766588876896899777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22904394044237005058399405 8589147766588876896899777)
            ·
              refine ⟨6441860824941657672674833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8589147766588876896899777 6441860824941657672674833)
              ·
                refine ⟨4831395618706243254506125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6441860824941657672674833 4831395618706243254506125)
                ·
                  refine ⟨1811773357014841220439797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4831395618706243254506125 1811773357014841220439797)
                  ·
                    refine ⟨169853752220141364416231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1811773357014841220439797 169853752220141364416231)
                    ·
                      rfl

theorem cell23_992367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 3, 5].length) (baseStart_992367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_992367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_992367 prefixEnd_992367 := by exact prefixLift 992367
  have htrace : WordTrace (prefixWord ++ tailWord_992367) baseStart_992367 baseEnd_992367 := by
    simpa [prefixWord, tailWord_992367, baseEnd_992367] using wordTrace_append hprefix tailTrace_992367
  have hstable : (prefixWord ++ tailWord_992367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992367).length < 2 ^ (prefixWord ++ tailWord_992367).sum := by decide
  have hdescent : baseEnd_992367 < baseStart_992367 := by decide
  rcases family_descends (prefixWord ++ tailWord_992367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992384 : List Nat := [2, 1, 1, 2, 1, 3, 5, 2, 1, 5]
def baseStart_992384 : Nat := 118140960795 + 992384 * 2 ^ 59
def prefixEnd_992384 : Nat := 4983230072969 + 3 ^ 40 * 992384 * 2
def baseEnd_992384 : Nat := 169856661943850175578705

theorem tailTrace_992384 : CollatzResearch.WordTrace tailWord_992384 prefixEnd_992384 169856661943850175578705 := by
  unfold tailWord_992384
  simp only [CollatzResearch.WordTrace]
  refine ⟨18097609018384864269432103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24130145357846485692576137 18097609018384864269432103)
  ·
    refine ⟨27146413527577296404148155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18097609018384864269432103 27146413527577296404148155)
    ·
      refine ⟨40719620291365944606222233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27146413527577296404148155 40719620291365944606222233)
      ·
        refine ⟨30539715218524458454666675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40719620291365944606222233 30539715218524458454666675)
        ·
          refine ⟨45809572827786687682000013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30539715218524458454666675 45809572827786687682000013)
          ·
            refine ⟨17178589810420007880750005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45809572827786687682000013 17178589810420007880750005)
            ·
              refine ⟨1610492794726875738820313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17178589810420007880750005 1610492794726875738820313)
              ·
                refine ⟨1207869596045156804115235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1610492794726875738820313 1207869596045156804115235)
                ·
                  refine ⟨1811804394067735206172853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1207869596045156804115235 1811804394067735206172853)
                  ·
                    refine ⟨169856661943850175578705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1811804394067735206172853 169856661943850175578705)
                    ·
                      rfl

theorem cell23_992384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 2, 1, 5].length) (baseStart_992384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_992384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_992384 prefixEnd_992384 := by exact prefixLift 992384
  have htrace : WordTrace (prefixWord ++ tailWord_992384) baseStart_992384 baseEnd_992384 := by
    simpa [prefixWord, tailWord_992384, baseEnd_992384] using wordTrace_append hprefix tailTrace_992384
  have hstable : (prefixWord ++ tailWord_992384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992384).length < 2 ^ (prefixWord ++ tailWord_992384).sum := by decide
  have hdescent : baseEnd_992384 < baseStart_992384 := by decide
  rcases family_descends (prefixWord ++ tailWord_992384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992415 : List Nat := [1, 1, 2, 6, 2, 1, 1, 4, 1, 1, 3]
def baseStart_992415 : Nat := 118140960795 + 992415 * 2 ^ 59
def prefixEnd_992415 : Nat := 4983230072969 + 3 ^ 40 * 992415 * 2
def baseEnd_992415 : Nat := 509585903731839905448473

theorem tailTrace_992415 : CollatzResearch.WordTrace tailWord_992415 prefixEnd_992415 509585903731839905448473 := by
  unfold tailWord_992415
  simp only [CollatzResearch.WordTrace]
  refine ⟨36196348699657420833242699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24130899133104947222161799 36196348699657420833242699)
  ·
    refine ⟨54294523049486131249864049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36196348699657420833242699 54294523049486131249864049)
    ·
      refine ⟨40720892287114598437398037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54294523049486131249864049 40720892287114598437398037)
      ·
        refine ⟨1908791825958496801753033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 40720892287114598437398037 1908791825958496801753033)
        ·
          refine ⟨1431593869468872601314775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1908791825958496801753033 1431593869468872601314775)
          ·
            refine ⟨2147390804203308901972163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1431593869468872601314775 2147390804203308901972163)
            ·
              refine ⟨3221086206304963352958245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2147390804203308901972163 3221086206304963352958245)
              ·
                refine ⟨603953663682180628679671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3221086206304963352958245 603953663682180628679671)
                ·
                  refine ⟨905930495523270943019507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 603953663682180628679671 905930495523270943019507)
                  ·
                    refine ⟨1358895743284906414529261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 905930495523270943019507 1358895743284906414529261)
                    ·
                      refine ⟨509585903731839905448473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1358895743284906414529261 509585903731839905448473)
                      ·
                        rfl

theorem cell23_992415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_992415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_992415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_992415 prefixEnd_992415 := by exact prefixLift 992415
  have htrace : WordTrace (prefixWord ++ tailWord_992415) baseStart_992415 baseEnd_992415 := by
    simpa [prefixWord, tailWord_992415, baseEnd_992415] using wordTrace_append hprefix tailTrace_992415
  have hstable : (prefixWord ++ tailWord_992415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992415).length < 2 ^ (prefixWord ++ tailWord_992415).sum := by decide
  have hdescent : baseEnd_992415 < baseStart_992415 := by decide
  rcases family_descends (prefixWord ++ tailWord_992415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992434 : List Nat := [3, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4]
def baseStart_992434 : Nat := 118140960795 + 992434 * 2 ^ 59
def prefixEnd_992434 : Nat := 4983230072969 + 3 ^ 40 * 992434 * 2
def baseEnd_992434 : Nat := 509595659864275331110885

theorem tailTrace_992434 : CollatzResearch.WordTrace tailWord_992434 prefixEnd_992434 509595659864275331110885 := by
  unfold tailWord_992434
  simp only [CollatzResearch.WordTrace]
  refine ⟨9049260421647146769546089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24131361124392391385456237 9049260421647146769546089)
  ·
    refine ⟨6786945316235360077159567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9049260421647146769546089 6786945316235360077159567)
    ·
      refine ⟨10180417974353040115739351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6786945316235360077159567 10180417974353040115739351)
      ·
        refine ⟨15270626961529560173609027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10180417974353040115739351 15270626961529560173609027)
        ·
          refine ⟨22905940442294340260413541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15270626961529560173609027 22905940442294340260413541)
          ·
            refine ⟨4294863832930188798827539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22905940442294340260413541 4294863832930188798827539)
            ·
              refine ⟨6442295749395283198241309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4294863832930188798827539 6442295749395283198241309)
              ·
                refine ⟨2415860906023231199340491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6442295749395283198241309 2415860906023231199340491)
                ·
                  refine ⟨3623791359034846799010737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2415860906023231199340491 3623791359034846799010737)
                  ·
                    refine ⟨2717843519276135099258053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3623791359034846799010737 2717843519276135099258053)
                    ·
                      refine ⟨509595659864275331110885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2717843519276135099258053 509595659864275331110885)
                      ·
                        rfl

theorem cell23_992434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_992434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_992434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_992434 prefixEnd_992434 := by exact prefixLift 992434
  have htrace : WordTrace (prefixWord ++ tailWord_992434) baseStart_992434 baseEnd_992434 := by
    simpa [prefixWord, tailWord_992434, baseEnd_992434] using wordTrace_append hprefix tailTrace_992434
  have hstable : (prefixWord ++ tailWord_992434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992434).length < 2 ^ (prefixWord ++ tailWord_992434).sum := by decide
  have hdescent : baseEnd_992434 < baseStart_992434 := by decide
  rcases family_descends (prefixWord ++ tailWord_992434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992458 : List Nat := [3, 1, 2, 1, 3, 2, 4, 1, 1, 2, 3]
def baseStart_992458 : Nat := 118140960795 + 992458 * 2 ^ 59
def prefixEnd_992458 : Nat := 4983230072969 + 3 ^ 40 * 992458 * 2
def baseEnd_992458 : Nat := 509607983399983237210775

theorem tailTrace_992458 : CollatzResearch.WordTrace tailWord_992458 prefixEnd_992458 509607983399983237210775 := by
  unfold tailWord_992458
  simp only [CollatzResearch.WordTrace]
  refine ⟨9049479259625409794264507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24131944692334426118038685 9049479259625409794264507)
  ·
    refine ⟨13574218889438114691396761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9049479259625409794264507 13574218889438114691396761)
    ·
      refine ⟨10180664167078586018547571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13574218889438114691396761 10180664167078586018547571)
      ·
        refine ⟨15270996250617879027821357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10180664167078586018547571 15270996250617879027821357)
        ·
          refine ⟨5726623593981704635433009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15270996250617879027821357 5726623593981704635433009)
          ·
            refine ⟨4294967695486278476574757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5726623593981704635433009 4294967695486278476574757)
            ·
              refine ⟨805306442903677214357767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4294967695486278476574757 805306442903677214357767)
              ·
                refine ⟨1207959664355515821536651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 805306442903677214357767 1207959664355515821536651)
                ·
                  refine ⟨1811939496533273732304977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1207959664355515821536651 1811939496533273732304977)
                  ·
                    refine ⟨1358954622399955299228733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1811939496533273732304977 1358954622399955299228733)
                    ·
                      refine ⟨509607983399983237210775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1358954622399955299228733 509607983399983237210775)
                      ·
                        rfl

theorem cell23_992458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 1, 1, 2, 3].length) (baseStart_992458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_992458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_992458 prefixEnd_992458 := by exact prefixLift 992458
  have htrace : WordTrace (prefixWord ++ tailWord_992458) baseStart_992458 baseEnd_992458 := by
    simpa [prefixWord, tailWord_992458, baseEnd_992458] using wordTrace_append hprefix tailTrace_992458
  have hstable : (prefixWord ++ tailWord_992458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992458).length < 2 ^ (prefixWord ++ tailWord_992458).sum := by decide
  have hdescent : baseEnd_992458 < baseStart_992458 := by decide
  rcases family_descends (prefixWord ++ tailWord_992458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992467 : List Nat := [1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 5]
def baseStart_992467 : Nat := 118140960795 + 992467 * 2 ^ 59
def prefixEnd_992467 : Nat := 4983230072969 + 3 ^ 40 * 992467 * 2
def baseEnd_992467 : Nat := 509612604725873701998233

theorem tailTrace_992467 : CollatzResearch.WordTrace tailWord_992467 prefixEnd_992467 509612604725873701998233 := by
  unfold tailWord_992467
  simp only [CollatzResearch.WordTrace]
  refine ⟨36198245295469033714135655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24132163530312689142757103 36198245295469033714135655)
  ·
    refine ⟨54297367943203550571203483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36198245295469033714135655 54297367943203550571203483)
    ·
      refine ⟨81446051914805325856805225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54297367943203550571203483 81446051914805325856805225)
      ·
        refine ⟨61084538936103994392603919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81446051914805325856805225 61084538936103994392603919)
        ·
          refine ⟨91626808404155991588905879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61084538936103994392603919 91626808404155991588905879)
          ·
            refine ⟨137440212606233987383358819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91626808404155991588905879 137440212606233987383358819)
            ·
              refine ⟨206160318909350981075038229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137440212606233987383358819 206160318909350981075038229)
              ·
                refine ⟨9663764948875827237892417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 206160318909350981075038229 9663764948875827237892417)
                ·
                  refine ⟨7247823711656870428419313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9663764948875827237892417 7247823711656870428419313)
                  ·
                    refine ⟨5435867783742652821314485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7247823711656870428419313 5435867783742652821314485)
                    ·
                      refine ⟨509612604725873701998233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5435867783742652821314485 509612604725873701998233)
                      ·
                        rfl

theorem cell23_992467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 5].length) (baseStart_992467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_992467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_992467 prefixEnd_992467 := by exact prefixLift 992467
  have htrace : WordTrace (prefixWord ++ tailWord_992467) baseStart_992467 baseEnd_992467 := by
    simpa [prefixWord, tailWord_992467, baseEnd_992467] using wordTrace_append hprefix tailTrace_992467
  have hstable : (prefixWord ++ tailWord_992467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992467).length < 2 ^ (prefixWord ++ tailWord_992467).sum := by decide
  have hdescent : baseEnd_992467 < baseStart_992467 := by decide
  rcases family_descends (prefixWord ++ tailWord_992467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992494 : List Nat := [4, 1, 2, 1, 1, 1, 2, 2, 2, 3, 4]
def baseStart_992494 : Nat := 118140960795 + 992494 * 2 ^ 59
def prefixEnd_992494 : Nat := 4983230072969 + 3 ^ 40 * 992494 * 2
def baseEnd_992494 : Nat := 509626468703545096360609

theorem tailTrace_992494 : CollatzResearch.WordTrace tailWord_992494 prefixEnd_992494 509626468703545096360609 := by
  unfold tailWord_992494
  simp only [CollatzResearch.WordTrace]
  refine ⟨4524903758296402165671067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24132820044247478216912357 4524903758296402165671067)
  ·
    refine ⟨6787355637444603248506601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4524903758296402165671067 6787355637444603248506601)
    ·
      refine ⟨5090516728083452436379951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6787355637444603248506601 5090516728083452436379951)
      ·
        refine ⟨7635775092125178654569927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5090516728083452436379951 7635775092125178654569927)
        ·
          refine ⟨11453662638187767981854891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7635775092125178654569927 11453662638187767981854891)
          ·
            refine ⟨17180493957281651972782337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11453662638187767981854891 17180493957281651972782337)
            ·
              refine ⟨12885370467961238979586753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17180493957281651972782337 12885370467961238979586753)
              ·
                refine ⟨9664027850970929234690065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12885370467961238979586753 9664027850970929234690065)
                ·
                  refine ⟨7248020888228196926017549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9664027850970929234690065 7248020888228196926017549)
                  ·
                    refine ⟨2718007833085573847256581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7248020888228196926017549 2718007833085573847256581)
                    ·
                      refine ⟨509626468703545096360609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2718007833085573847256581 509626468703545096360609)
                      ·
                        rfl

theorem cell23_992494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_992494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_992494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_992494 prefixEnd_992494 := by exact prefixLift 992494
  have htrace : WordTrace (prefixWord ++ tailWord_992494) baseStart_992494 baseEnd_992494 := by
    simpa [prefixWord, tailWord_992494, baseEnd_992494] using wordTrace_append hprefix tailTrace_992494
  have hstable : (prefixWord ++ tailWord_992494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992494).length < 2 ^ (prefixWord ++ tailWord_992494).sum := by decide
  have hdescent : baseEnd_992494 < baseStart_992494 := by decide
  rcases family_descends (prefixWord ++ tailWord_992494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992584 : List Nat := [2, 1, 3, 1, 1, 2, 1, 2, 3, 3, 4]
def baseStart_992584 : Nat := 118140960795 + 992584 * 2 ^ 59
def prefixEnd_992584 : Nat := 4983230072969 + 3 ^ 40 * 992584 * 2
def baseEnd_992584 : Nat := 509672681962449744235195

theorem tailTrace_992584 : CollatzResearch.WordTrace tailWord_992584 prefixEnd_992584 509672681962449744235195 := by
  unfold tailWord_992584
  simp only [CollatzResearch.WordTrace]
  refine ⟨18101256318022581348072403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24135008424030108464096537 18101256318022581348072403)
  ·
    refine ⟨27151884477033872022108605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18101256318022581348072403 27151884477033872022108605)
    ·
      refine ⟨10181956678887702008290727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27151884477033872022108605 10181956678887702008290727)
      ·
        refine ⟨15272935018331553012436091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10181956678887702008290727 15272935018331553012436091)
        ·
          refine ⟨22909402527497329518654137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15272935018331553012436091 22909402527497329518654137)
          ·
            refine ⟨17182051895622997138990603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22909402527497329518654137 17182051895622997138990603)
            ·
              refine ⟨25773077843434495708485905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17182051895622997138990603 25773077843434495708485905)
              ·
                refine ⟨19329808382575871781364429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25773077843434495708485905 19329808382575871781364429)
                ·
                  refine ⟨7248678143465951918011661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19329808382575871781364429 7248678143465951918011661)
                  ·
                    refine ⟨2718254303799731969254373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7248678143465951918011661 2718254303799731969254373)
                    ·
                      refine ⟨509672681962449744235195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2718254303799731969254373 509672681962449744235195)
                      ·
                        rfl

theorem cell23_992584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_992584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_992584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_992584 prefixEnd_992584 := by exact prefixLift 992584
  have htrace : WordTrace (prefixWord ++ tailWord_992584) baseStart_992584 baseEnd_992584 := by
    simpa [prefixWord, tailWord_992584, baseEnd_992584] using wordTrace_append hprefix tailTrace_992584
  have hstable : (prefixWord ++ tailWord_992584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992584).length < 2 ^ (prefixWord ++ tailWord_992584).sum := by decide
  have hdescent : baseEnd_992584 < baseStart_992584 := by decide
  rcases family_descends (prefixWord ++ tailWord_992584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992594 : List Nat := [3, 2, 2, 1, 1, 1, 1, 2, 2, 8]
def baseStart_992594 : Nat := 118140960795 + 992594 * 2 ^ 59
def prefixEnd_992594 : Nat := 4983230072969 + 3 ^ 40 * 992594 * 2
def baseEnd_992594 : Nat := 169892605589664901703383

theorem tailTrace_992594 : CollatzResearch.WordTrace tailWord_992594 prefixEnd_992594 169892605589664901703383 := by
  unfold tailWord_992594
  simp only [CollatzResearch.WordTrace]
  refine ⟨9050719341502233601002209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24135251577339289602672557 9050719341502233601002209)
  ·
    refine ⟨6788039506126675200751657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9050719341502233601002209 6788039506126675200751657)
    ·
      refine ⟨5091029629595006400563743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6788039506126675200751657 5091029629595006400563743)
      ·
        refine ⟨7636544444392509600845615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5091029629595006400563743 7636544444392509600845615)
        ·
          refine ⟨11454816666588764401268423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7636544444392509600845615 11454816666588764401268423)
          ·
            refine ⟨17182224999883146601902635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11454816666588764401268423 17182224999883146601902635)
            ·
              refine ⟨25773337499824719902853953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17182224999883146601902635 25773337499824719902853953)
              ·
                refine ⟨19330003124868539927140465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25773337499824719902853953 19330003124868539927140465)
                ·
                  refine ⟨14497502343651404945355349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19330003124868539927140465 14497502343651404945355349)
                  ·
                    refine ⟨169892605589664901703383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 14497502343651404945355349 169892605589664901703383)
                    ·
                      rfl

theorem cell23_992594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_992594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_992594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_992594 prefixEnd_992594 := by exact prefixLift 992594
  have htrace : WordTrace (prefixWord ++ tailWord_992594) baseStart_992594 baseEnd_992594 := by
    simpa [prefixWord, tailWord_992594, baseEnd_992594] using wordTrace_append hprefix tailTrace_992594
  have hstable : (prefixWord ++ tailWord_992594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992594).length < 2 ^ (prefixWord ++ tailWord_992594).sum := by decide
  have hdescent : baseEnd_992594 < baseStart_992594 := by decide
  rcases family_descends (prefixWord ++ tailWord_992594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992601 : List Nat := [1, 2, 1, 2, 2, 2, 3, 1, 1, 6, 2]
def baseStart_992601 : Nat := 118140960795 + 992601 * 2 ^ 59
def prefixEnd_992601 : Nat := 4983230072969 + 3 ^ 40 * 992601 * 2
def baseEnd_992601 : Nat := 509681411133576177722617

theorem tailTrace_992601 : CollatzResearch.WordTrace tailWord_992601 prefixEnd_992601 509681411133576177722617 := by
  unfold tailWord_992601
  simp only [CollatzResearch.WordTrace]
  refine ⟨36203132676983574599513657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24135421784655716399675771 36203132676983574599513657)
  ·
    refine ⟨27152349507737680949635243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36203132676983574599513657 27152349507737680949635243)
    ·
      refine ⟨40728524261606521424452865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27152349507737680949635243 40728524261606521424452865)
      ·
        refine ⟨30546393196204891068339649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40728524261606521424452865 30546393196204891068339649)
        ·
          refine ⟨22909794897153668301254737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30546393196204891068339649 22909794897153668301254737)
          ·
            refine ⟨17182346172865251225941053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22909794897153668301254737 17182346172865251225941053)
            ·
              refine ⟨6443379814824469209727895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17182346172865251225941053 6443379814824469209727895)
              ·
                refine ⟨9665069722236703814591843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6443379814824469209727895 9665069722236703814591843)
                ·
                  refine ⟨14497604583355055721887765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9665069722236703814591843 14497604583355055721887765)
                  ·
                    refine ⟨679575214844768236963489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14497604583355055721887765 679575214844768236963489)
                    ·
                      refine ⟨509681411133576177722617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 679575214844768236963489 509681411133576177722617)
                      ·
                        rfl

theorem cell23_992601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 6, 2].length) (baseStart_992601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_992601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_992601 prefixEnd_992601 := by exact prefixLift 992601
  have htrace : WordTrace (prefixWord ++ tailWord_992601) baseStart_992601 baseEnd_992601 := by
    simpa [prefixWord, tailWord_992601, baseEnd_992601] using wordTrace_append hprefix tailTrace_992601
  have hstable : (prefixWord ++ tailWord_992601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992601).length < 2 ^ (prefixWord ++ tailWord_992601).sum := by decide
  have hdescent : baseEnd_992601 < baseStart_992601 := by decide
  rcases family_descends (prefixWord ++ tailWord_992601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992611 : List Nat := [1, 1, 1, 5, 2, 2, 1, 1, 5, 4]
def baseStart_992611 : Nat := 118140960795 + 992611 * 2 ^ 59
def prefixEnd_992611 : Nat := 4983230072969 + 3 ^ 40 * 992611 * 2
def baseEnd_992611 : Nat := 169895515313373712865857

theorem tailTrace_992611 : CollatzResearch.WordTrace tailWord_992611 prefixEnd_992611 169895515313373712865857 := by
  unfold tailWord_992611
  simp only [CollatzResearch.WordTrace]
  refine ⟨36203497406947346307377687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24135664937964897538251791 36203497406947346307377687)
  ·
    refine ⟨54305246110421019461066531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36203497406947346307377687 54305246110421019461066531)
    ·
      refine ⟨81457869165631529191599797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54305246110421019461066531 81457869165631529191599797)
      ·
        refine ⟨7636675234277955861712481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81457869165631529191599797 7636675234277955861712481)
        ·
          refine ⟨5727506425708466896284361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7636675234277955861712481 5727506425708466896284361)
          ·
            refine ⟨4295629819281350172213271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5727506425708466896284361 4295629819281350172213271)
            ·
              refine ⟨6443444728922025258319907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4295629819281350172213271 6443444728922025258319907)
              ·
                refine ⟨9665167093383037887479861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6443444728922025258319907 9665167093383037887479861)
                ·
                  refine ⟨906109415004659801951237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9665167093383037887479861 906109415004659801951237)
                  ·
                    refine ⟨169895515313373712865857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 906109415004659801951237 169895515313373712865857)
                    ·
                      rfl

theorem cell23_992611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 5, 4].length) (baseStart_992611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_992611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_992611 prefixEnd_992611 := by exact prefixLift 992611
  have htrace : WordTrace (prefixWord ++ tailWord_992611) baseStart_992611 baseEnd_992611 := by
    simpa [prefixWord, tailWord_992611, baseEnd_992611] using wordTrace_append hprefix tailTrace_992611
  have hstable : (prefixWord ++ tailWord_992611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992611).length < 2 ^ (prefixWord ++ tailWord_992611).sum := by decide
  have hdescent : baseEnd_992611 < baseStart_992611 := by decide
  rcases family_descends (prefixWord ++ tailWord_992611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992615 : List Nat := [1, 1, 5, 1, 5, 1, 1, 1, 2, 5]
def baseStart_992615 : Nat := 118140960795 + 992615 * 2 ^ 59
def prefixEnd_992615 : Nat := 4983230072969 + 3 ^ 40 * 992615 * 2
def baseEnd_992615 : Nat := 169896199954246374315851

theorem tailTrace_992615 : CollatzResearch.WordTrace tailWord_992615 prefixEnd_992615 169896199954246374315851 := by
  unfold tailWord_992615
  simp only [CollatzResearch.WordTrace]
  refine ⟨36203643298932854990523299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24135762199288569993682199 36203643298932854990523299)
  ·
    refine ⟨54305464948399282485784949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36203643298932854990523299 54305464948399282485784949)
    ·
      refine ⟨5091137338912432733042339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54305464948399282485784949 5091137338912432733042339)
      ·
        refine ⟨7636706008368649099563509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5091137338912432733042339 7636706008368649099563509)
        ·
          refine ⟨715941188284560853084079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7636706008368649099563509 715941188284560853084079)
          ·
            refine ⟨1073911782426841279626119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 715941188284560853084079 1073911782426841279626119)
            ·
              refine ⟨1610867673640261919439179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1073911782426841279626119 1610867673640261919439179)
              ·
                refine ⟨2416301510460392879158769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1610867673640261919439179 2416301510460392879158769)
                ·
                  refine ⟨1812226132845294659369077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2416301510460392879158769 1812226132845294659369077)
                  ·
                    refine ⟨169896199954246374315851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1812226132845294659369077 169896199954246374315851)
                    ·
                      rfl

theorem cell23_992615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_992615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_992615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_992615 prefixEnd_992615 := by exact prefixLift 992615
  have htrace : WordTrace (prefixWord ++ tailWord_992615) baseStart_992615 baseEnd_992615 := by
    simpa [prefixWord, tailWord_992615, baseEnd_992615] using wordTrace_append hprefix tailTrace_992615
  have hstable : (prefixWord ++ tailWord_992615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992615).length < 2 ^ (prefixWord ++ tailWord_992615).sum := by decide
  have hdescent : baseEnd_992615 < baseStart_992615 := by decide
  rcases family_descends (prefixWord ++ tailWord_992615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992618 : List Nat := [3, 1, 3, 3, 2, 1, 1, 1, 1, 3, 4]
def baseStart_992618 : Nat := 118140960795 + 992618 * 2 ^ 59
def prefixEnd_992618 : Nat := 4983230072969 + 3 ^ 40 * 992618 * 2
def baseEnd_992618 : Nat := 509690140304702611210039

theorem tailTrace_992618 : CollatzResearch.WordTrace tailWord_992618 prefixEnd_992618 509690140304702611210039 := by
  unfold tailWord_992618
  simp only [CollatzResearch.WordTrace]
  refine ⟨9050938179480496625720627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24135835145281324335255005 9050938179480496625720627)
  ·
    refine ⟨13576407269220744938580941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9050938179480496625720627 13576407269220744938580941)
    ·
      refine ⟨5091152725957779351967853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13576407269220744938580941 5091152725957779351967853)
      ·
        refine ⟨1909182272234167256987945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5091152725957779351967853 1909182272234167256987945)
        ·
          refine ⟨1431886704175625442740959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1909182272234167256987945 1431886704175625442740959)
          ·
            refine ⟨2147830056263438164111439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1431886704175625442740959 2147830056263438164111439)
            ·
              refine ⟨3221745084395157246167159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2147830056263438164111439 3221745084395157246167159)
              ·
                refine ⟨4832617626592735869250739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3221745084395157246167159 4832617626592735869250739)
                ·
                  refine ⟨7248926439889103803876109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4832617626592735869250739 7248926439889103803876109)
                  ·
                    refine ⟨2718347414958413926453541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7248926439889103803876109 2718347414958413926453541)
                    ·
                      refine ⟨509690140304702611210039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2718347414958413926453541 509690140304702611210039)
                      ·
                        rfl

theorem cell23_992618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_992618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_992618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_992618 prefixEnd_992618 := by exact prefixLift 992618
  have htrace : WordTrace (prefixWord ++ tailWord_992618) baseStart_992618 baseEnd_992618 := by
    simpa [prefixWord, tailWord_992618, baseEnd_992618] using wordTrace_append hprefix tailTrace_992618
  have hstable : (prefixWord ++ tailWord_992618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992618).length < 2 ^ (prefixWord ++ tailWord_992618).sum := by decide
  have hdescent : baseEnd_992618 < baseStart_992618 := by decide
  rcases family_descends (prefixWord ++ tailWord_992618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992624 : List Nat := [2, 1, 1, 1, 4, 2, 2, 2, 8]
def baseStart_992624 : Nat := 118140960795 + 992624 * 2 ^ 59
def prefixEnd_992624 : Nat := 4983230072969 + 3 ^ 40 * 992624 * 2
def baseEnd_992624 : Nat := 56632580132069954192779

theorem tailTrace_992624 : CollatzResearch.WordTrace tailWord_992624 prefixEnd_992624 56632580132069954192779 := by
  unfold tailWord_992624
  simp only [CollatzResearch.WordTrace]
  refine ⟨18101985777950124763800463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24135981037266833018400617 18101985777950124763800463)
  ·
    refine ⟨27152978666925187145700695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18101985777950124763800463 27152978666925187145700695)
    ·
      refine ⟨40729468000387780718551043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27152978666925187145700695 40729468000387780718551043)
      ·
        refine ⟨61094202000581671077826565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40729468000387780718551043 61094202000581671077826565)
        ·
          refine ⟨11455162875109063327092481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61094202000581671077826565 11455162875109063327092481)
          ·
            refine ⟨8591372156331797495319361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11455162875109063327092481 8591372156331797495319361)
            ·
              refine ⟨6443529117248848121489521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8591372156331797495319361 6443529117248848121489521)
              ·
                refine ⟨4832646837936636091117141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6443529117248848121489521 4832646837936636091117141)
                ·
                  refine ⟨56632580132069954192779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4832646837936636091117141 56632580132069954192779)
                  ·
                    rfl

theorem cell23_992624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 8].length) (baseStart_992624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_992624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_992624 prefixEnd_992624 := by exact prefixLift 992624
  have htrace : WordTrace (prefixWord ++ tailWord_992624) baseStart_992624 baseEnd_992624 := by
    simpa [prefixWord, tailWord_992624, baseEnd_992624] using wordTrace_append hprefix tailTrace_992624
  have hstable : (prefixWord ++ tailWord_992624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992624).length < 2 ^ (prefixWord ++ tailWord_992624).sum := by decide
  have hdescent : baseEnd_992624 < baseStart_992624 := by decide
  rcases family_descends (prefixWord ++ tailWord_992624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992711 : List Nat := [1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 5]
def baseStart_992711 : Nat := 118140960795 + 992711 * 2 ^ 59
def prefixEnd_992711 : Nat := 4983230072969 + 3 ^ 40 * 992711 * 2
def baseEnd_992711 : Nat := 509737894005570747347111

theorem tailTrace_992711 : CollatzResearch.WordTrace tailWord_992711 prefixEnd_992711 509737894005570747347111 := by
  unfold tailWord_992711
  simp only [CollatzResearch.WordTrace]
  refine ⟨36207144706585063386017987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24138096471056708924011991 36207144706585063386017987)
  ·
    refine ⟨54310717059877595079026981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36207144706585063386017987 54310717059877595079026981)
    ·
      refine ⟨10183259448727049077317559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54310717059877595079026981 10183259448727049077317559)
      ·
        refine ⟨15274889173090573615976339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10183259448727049077317559 15274889173090573615976339)
        ·
          refine ⟨22912333759635860423964509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15274889173090573615976339 22912333759635860423964509)
          ·
            refine ⟨8592125159863447658986691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22912333759635860423964509 8592125159863447658986691)
            ·
              refine ⟨12888187739795171488480037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8592125159863447658986691 12888187739795171488480037)
              ·
                refine ⟨2416535201211594654090007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12888187739795171488480037 2416535201211594654090007)
                ·
                  refine ⟨3624802801817391981135011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2416535201211594654090007 3624802801817391981135011)
                  ·
                    refine ⟨5437204202726087971702517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3624802801817391981135011 5437204202726087971702517)
                    ·
                      refine ⟨509737894005570747347111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5437204202726087971702517 509737894005570747347111)
                      ·
                        rfl

theorem cell23_992711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_992711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_992711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_992711 prefixEnd_992711 := by exact prefixLift 992711
  have htrace : WordTrace (prefixWord ++ tailWord_992711) baseStart_992711 baseEnd_992711 := by
    simpa [prefixWord, tailWord_992711, baseEnd_992711] using wordTrace_append hprefix tailTrace_992711
  have hstable : (prefixWord ++ tailWord_992711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992711).length < 2 ^ (prefixWord ++ tailWord_992711).sum := by decide
  have hdescent : baseEnd_992711 < baseStart_992711 := by decide
  rcases family_descends (prefixWord ++ tailWord_992711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992725 : List Nat := [1, 3, 2, 3, 1, 1, 2, 1, 5, 2, 2]
def baseStart_992725 : Nat := 118140960795 + 992725 * 2 ^ 59
def prefixEnd_992725 : Nat := 4983230072969 + 3 ^ 40 * 992725 * 2
def baseEnd_992725 : Nat := 509745082734733692572047

theorem tailTrace_992725 : CollatzResearch.WordTrace tailWord_992725 prefixEnd_992725 509745082734733692572047 := by
  unfold tailWord_992725
  simp only [CollatzResearch.WordTrace]
  refine ⟨36207655328534343777027629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24138436885689562518018419 36207655328534343777027629)
  ·
    refine ⟨13577870748200378916385361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36207655328534343777027629 13577870748200378916385361)
    ·
      refine ⟨10183403061150284187289021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13577870748200378916385361 10183403061150284187289021)
      ·
        refine ⟨3818776147931356570233383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10183403061150284187289021 3818776147931356570233383)
        ·
          refine ⟨5728164221897034855350075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3818776147931356570233383 5728164221897034855350075)
          ·
            refine ⟨8592246332845552283025113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5728164221897034855350075 8592246332845552283025113)
            ·
              refine ⟨6444184749634164212268835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8592246332845552283025113 6444184749634164212268835)
              ·
                refine ⟨9666277124451246318403253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6444184749634164212268835 9666277124451246318403253)
                ·
                  refine ⟨906213480417304342350305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9666277124451246318403253 906213480417304342350305)
                  ·
                    refine ⟨679660110312978256762729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 906213480417304342350305 679660110312978256762729)
                    ·
                      refine ⟨509745082734733692572047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 679660110312978256762729 509745082734733692572047)
                      ·
                        rfl

theorem cell23_992725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_992725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_992725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_992725 prefixEnd_992725 := by exact prefixLift 992725
  have htrace : WordTrace (prefixWord ++ tailWord_992725) baseStart_992725 baseEnd_992725 := by
    simpa [prefixWord, tailWord_992725, baseEnd_992725] using wordTrace_append hprefix tailTrace_992725
  have hstable : (prefixWord ++ tailWord_992725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992725).length < 2 ^ (prefixWord ++ tailWord_992725).sum := by decide
  have hdescent : baseEnd_992725 < baseStart_992725 := by decide
  rcases family_descends (prefixWord ++ tailWord_992725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992775 : List Nat := [1, 1, 4, 3, 2, 2, 2, 1, 1, 3, 3]
def baseStart_992775 : Nat := 118140960795 + 992775 * 2 ^ 59
def prefixEnd_992775 : Nat := 4983230072969 + 3 ^ 40 * 992775 * 2
def baseEnd_992775 : Nat := 509770756767458496946817

theorem tailTrace_992775 : CollatzResearch.WordTrace tailWord_992775 prefixEnd_992775 509770756767458496946817 := by
  unfold tailWord_992775
  simp only [CollatzResearch.WordTrace]
  refine ⟨36209478978353202316347779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24139652652235468210898519 36209478978353202316347779)
  ·
    refine ⟨54314218467529803474521669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36209478978353202316347779 54314218467529803474521669)
    ·
      refine ⟨10183915962661838151472813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54314218467529803474521669 10183915962661838151472813)
      ·
        refine ⟨3818968485998189306802305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10183915962661838151472813 3818968485998189306802305)
        ·
          refine ⟨2864226364498641980101729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3818968485998189306802305 2864226364498641980101729)
          ·
            refine ⟨2148169773373981485076297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2864226364498641980101729 2148169773373981485076297)
            ·
              refine ⟨1611127330030486113807223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2148169773373981485076297 1611127330030486113807223)
              ·
                refine ⟨2416690995045729170710835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1611127330030486113807223 2416690995045729170710835)
                ·
                  refine ⟨3625036492568593756066253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2416690995045729170710835 3625036492568593756066253)
                  ·
                    refine ⟨1359388684713222658524845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3625036492568593756066253 1359388684713222658524845)
                    ·
                      refine ⟨509770756767458496946817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1359388684713222658524845 509770756767458496946817)
                      ·
                        rfl

theorem cell23_992775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_992775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_992775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_992775 prefixEnd_992775 := by exact prefixLift 992775
  have htrace : WordTrace (prefixWord ++ tailWord_992775) baseStart_992775 baseEnd_992775 := by
    simpa [prefixWord, tailWord_992775, baseEnd_992775] using wordTrace_append hprefix tailTrace_992775
  have hstable : (prefixWord ++ tailWord_992775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992775).length < 2 ^ (prefixWord ++ tailWord_992775).sum := by decide
  have hdescent : baseEnd_992775 < baseStart_992775 := by decide
  rcases family_descends (prefixWord ++ tailWord_992775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992785 : List Nat := [1, 2, 2, 1, 1, 2, 4, 4, 1, 3, 2]
def baseStart_992785 : Nat := 118140960795 + 992785 * 2 ^ 59
def prefixEnd_992785 : Nat := 4983230072969 + 3 ^ 40 * 992785 * 2
def baseEnd_992785 : Nat := 509775891574003457821771

theorem tailTrace_992785 : CollatzResearch.WordTrace tailWord_992785 prefixEnd_992785 509775891574003457821771 := by
  unfold tailWord_992785
  simp only [CollatzResearch.WordTrace]
  refine ⟨36209843708316974024211809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24139895805544649349474539 36209843708316974024211809)
  ·
    refine ⟨27157382781237730518158857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36209843708316974024211809 27157382781237730518158857)
    ·
      refine ⟨20368037085928297888619143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27157382781237730518158857 20368037085928297888619143)
      ·
        refine ⟨30552055628892446832928715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20368037085928297888619143 30552055628892446832928715)
        ·
          refine ⟨45828083443338670249393073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30552055628892446832928715 45828083443338670249393073)
          ·
            refine ⟨34371062582504002687044805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45828083443338670249393073 34371062582504002687044805)
            ·
              refine ⟨6444574234219500503820901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34371062582504002687044805 6444574234219500503820901)
              ·
                refine ⟨1208357668916156344466419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6444574234219500503820901 1208357668916156344466419)
                ·
                  refine ⟨1812536503374234516699629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1208357668916156344466419 1812536503374234516699629)
                  ·
                    refine ⟨679701188765337943762361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1812536503374234516699629 679701188765337943762361)
                    ·
                      refine ⟨509775891574003457821771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 679701188765337943762361 509775891574003457821771)
                      ·
                        rfl

theorem cell23_992785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 3, 2].length) (baseStart_992785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_992785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_992785 prefixEnd_992785 := by exact prefixLift 992785
  have htrace : WordTrace (prefixWord ++ tailWord_992785) baseStart_992785 baseEnd_992785 := by
    simpa [prefixWord, tailWord_992785, baseEnd_992785] using wordTrace_append hprefix tailTrace_992785
  have hstable : (prefixWord ++ tailWord_992785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992785).length < 2 ^ (prefixWord ++ tailWord_992785).sum := by decide
  have hdescent : baseEnd_992785 < baseStart_992785 := by decide
  rcases family_descends (prefixWord ++ tailWord_992785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992855 : List Nat := [1, 1, 3, 2, 2, 3, 3, 3, 5]
def baseStart_992855 : Nat := 118140960795 + 992855 * 2 ^ 59
def prefixEnd_992855 : Nat := 4983230072969 + 3 ^ 40 * 992855 * 2
def baseEnd_992855 : Nat := 56645759468868687105161

theorem tailTrace_992855 : CollatzResearch.WordTrace tailWord_992855 prefixEnd_992855 56645759468868687105161 := by
  unfold tailWord_992855
  simp only [CollatzResearch.WordTrace]
  refine ⟨36212396818063375979260019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24141597878708917319506679 36212396818063375979260019)
  ·
    refine ⟨54318595227095063968890029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36212396818063375979260019 54318595227095063968890029)
    ·
      refine ⟨20369473210160648988333761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54318595227095063968890029 20369473210160648988333761)
      ·
        refine ⟨15277104907620486741250321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20369473210160648988333761 15277104907620486741250321)
        ·
          refine ⟨11457828680715365055937741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15277104907620486741250321 11457828680715365055937741)
          ·
            refine ⟨4296685755268261895976653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11457828680715365055937741 4296685755268261895976653)
            ·
              refine ⟨1611257158225598210991245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4296685755268261895976653 1611257158225598210991245)
              ·
                refine ⟨604221434334599329121717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1611257158225598210991245 604221434334599329121717)
                ·
                  refine ⟨56645759468868687105161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 604221434334599329121717 56645759468868687105161)
                  ·
                    rfl

theorem cell23_992855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 3, 5].length) (baseStart_992855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_992855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_992855 prefixEnd_992855 := by exact prefixLift 992855
  have htrace : WordTrace (prefixWord ++ tailWord_992855) baseStart_992855 baseEnd_992855 := by
    simpa [prefixWord, tailWord_992855, baseEnd_992855] using wordTrace_append hprefix tailTrace_992855
  have hstable : (prefixWord ++ tailWord_992855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992855).length < 2 ^ (prefixWord ++ tailWord_992855).sum := by decide
  have hdescent : baseEnd_992855 < baseStart_992855 := by decide
  rcases family_descends (prefixWord ++ tailWord_992855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992868 : List Nat := [2, 3, 1, 1, 2, 3, 1, 1, 4, 5]
def baseStart_992868 : Nat := 118140960795 + 992868 * 2 ^ 59
def prefixEnd_992868 : Nat := 4983230072969 + 3 ^ 40 * 992868 * 2
def baseEnd_992868 : Nat := 169939503489442211027963

theorem tailTrace_992868 : CollatzResearch.WordTrace tailWord_992868 prefixEnd_992868 169939503489442211027963 := by
  unfold tailWord_992868
  simp only [CollatzResearch.WordTrace]
  refine ⟨18106435483508139599741629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24141913978010852799655505 18106435483508139599741629)
  ·
    refine ⟨6789913306315552349903111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18106435483508139599741629 6789913306315552349903111)
    ·
      refine ⟨10184869959473328524854667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6789913306315552349903111 10184869959473328524854667)
      ·
        refine ⟨15277304939209992787282001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10184869959473328524854667 15277304939209992787282001)
        ·
          refine ⟨11457978704407494590461501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15277304939209992787282001 11457978704407494590461501)
          ·
            refine ⟨4296742014152810471423063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11457978704407494590461501 4296742014152810471423063)
            ·
              refine ⟨6445113021229215707134595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4296742014152810471423063 6445113021229215707134595)
              ·
                refine ⟨9667669531843823560701893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6445113021229215707134595 9667669531843823560701893)
                ·
                  refine ⟨1812688037220716917631605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9667669531843823560701893 1812688037220716917631605)
                  ·
                    refine ⟨169939503489442211027963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1812688037220716917631605 169939503489442211027963)
                    ·
                      rfl

theorem cell23_992868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 4, 5].length) (baseStart_992868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_992868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_992868 prefixEnd_992868 := by exact prefixLift 992868
  have htrace : WordTrace (prefixWord ++ tailWord_992868) baseStart_992868 baseEnd_992868 := by
    simpa [prefixWord, tailWord_992868, baseEnd_992868] using wordTrace_append hprefix tailTrace_992868
  have hstable : (prefixWord ++ tailWord_992868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992868).length < 2 ^ (prefixWord ++ tailWord_992868).sum := by decide
  have hdescent : baseEnd_992868 < baseStart_992868 := by decide
  rcases family_descends (prefixWord ++ tailWord_992868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_992965 : List Nat := [1, 3, 1, 1, 1, 1, 2, 5, 1, 5, 2]
def baseStart_992965 : Nat := 118140960795 + 992965 * 2 ^ 59
def prefixEnd_992965 : Nat := 4983230072969 + 3 ^ 40 * 992965 * 2
def baseEnd_992965 : Nat := 509868318091812753570943

theorem tailTrace_992965 : CollatzResearch.WordTrace tailWord_992965 prefixEnd_992965 509868318091812753570943 := by
  unfold tailWord_992965
  simp only [CollatzResearch.WordTrace]
  refine ⟨36216408847664864765764349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24144272565109909843842899 36216408847664864765764349)
  ·
    refine ⟨13581153317874324287161631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36216408847664864765764349 13581153317874324287161631)
    ·
      refine ⟨20371729976811486430742447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13581153317874324287161631 20371729976811486430742447)
      ·
        refine ⟨30557594965217229646113671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20371729976811486430742447 30557594965217229646113671)
        ·
          refine ⟨45836392447825844469170507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30557594965217229646113671 45836392447825844469170507)
          ·
            refine ⟨68754588671738766703755761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45836392447825844469170507 68754588671738766703755761)
            ·
              refine ⟨51565941503804075027816821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68754588671738766703755761 51565941503804075027816821)
              ·
                refine ⟨4834307015981632033857827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51565941503804075027816821 4834307015981632033857827)
                ·
                  refine ⟨7251460523972448050786741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4834307015981632033857827 7251460523972448050786741)
                  ·
                    refine ⟨679824424122417004761257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7251460523972448050786741 679824424122417004761257)
                    ·
                      refine ⟨509868318091812753570943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 679824424122417004761257 509868318091812753570943)
                      ·
                        rfl

theorem cell23_992965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 5, 2].length) (baseStart_992965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_992965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_992965 prefixEnd_992965 := by exact prefixLift 992965
  have htrace : WordTrace (prefixWord ++ tailWord_992965) baseStart_992965 baseEnd_992965 := by
    simpa [prefixWord, tailWord_992965, baseEnd_992965] using wordTrace_append hprefix tailTrace_992965
  have hstable : (prefixWord ++ tailWord_992965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_992965).length < 2 ^ (prefixWord ++ tailWord_992965).sum := by decide
  have hdescent : baseEnd_992965 < baseStart_992965 := by decide
  rcases family_descends (prefixWord ++ tailWord_992965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993015 : List Nat := [1, 1, 3, 1, 1, 1, 4, 3, 3, 2, 3]
def baseStart_993015 : Nat := 118140960795 + 993015 * 2 ^ 59
def prefixEnd_993015 : Nat := 4983230072969 + 3 ^ 40 * 993015 * 2
def baseEnd_993015 : Nat := 509893992124537557945713

theorem tailTrace_993015 : CollatzResearch.WordTrace tailWord_993015 prefixEnd_993015 509893992124537557945713 := by
  unfold tailWord_993015
  simp only [CollatzResearch.WordTrace]
  refine ⟨36218232497483723305084499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24145488331655815536722999 36218232497483723305084499)
  ·
    refine ⟨54327348746225584957626749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36218232497483723305084499 54327348746225584957626749)
    ·
      refine ⟨20372755779834594359110031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54327348746225584957626749 20372755779834594359110031)
      ·
        refine ⟨30559133669751891538665047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20372755779834594359110031 30559133669751891538665047)
        ·
          refine ⟨45838700504627837307997571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30559133669751891538665047 45838700504627837307997571)
          ·
            refine ⟨68758050756941755961996357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45838700504627837307997571 68758050756941755961996357)
            ·
              refine ⟨12892134516926579242874317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68758050756941755961996357 12892134516926579242874317)
              ·
                refine ⟨4834550443847467216077869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12892134516926579242874317 4834550443847467216077869)
                ·
                  refine ⟨1812956416442800206029201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4834550443847467216077869 1812956416442800206029201)
                  ·
                    refine ⟨1359717312332100154521901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1812956416442800206029201 1359717312332100154521901)
                    ·
                      refine ⟨509893992124537557945713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1359717312332100154521901 509893992124537557945713)
                      ·
                        rfl

theorem cell23_993015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 3, 2, 3].length) (baseStart_993015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_993015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_993015 prefixEnd_993015 := by exact prefixLift 993015
  have htrace : WordTrace (prefixWord ++ tailWord_993015) baseStart_993015 baseEnd_993015 := by
    simpa [prefixWord, tailWord_993015, baseEnd_993015] using wordTrace_append hprefix tailTrace_993015
  have hstable : (prefixWord ++ tailWord_993015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993015).length < 2 ^ (prefixWord ++ tailWord_993015).sum := by decide
  have hdescent : baseEnd_993015 < baseStart_993015 := by decide
  rcases family_descends (prefixWord ++ tailWord_993015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993025 : List Nat := [1, 2, 4, 1, 1, 1, 2, 4, 1, 2, 4]
def baseStart_993025 : Nat := 118140960795 + 993025 * 2 ^ 59
def prefixEnd_993025 : Nat := 4983230072969 + 3 ^ 40 * 993025 * 2
def baseEnd_993025 : Nat := 509899126931082518820667

theorem tailTrace_993025 : CollatzResearch.WordTrace tailWord_993025 prefixEnd_993025 509899126931082518820667 := by
  unfold tailWord_993025
  simp only [CollatzResearch.WordTrace]
  refine ⟨36218597227447495012948529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24145731484964996675299019 36218597227447495012948529)
  ·
    refine ⟨27163947920585621259711397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36218597227447495012948529 27163947920585621259711397)
    ·
      refine ⟨5093240235109803986195887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27163947920585621259711397 5093240235109803986195887)
      ·
        refine ⟨7639860352664705979293831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5093240235109803986195887 7639860352664705979293831)
        ·
          refine ⟨11459790528997058968940747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7639860352664705979293831 11459790528997058968940747)
          ·
            refine ⟨17189685793495588453411121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11459790528997058968940747 17189685793495588453411121)
            ·
              refine ⟨12892264345121691340058341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17189685793495588453411121 12892264345121691340058341)
              ·
                refine ⟨2417299564710317126260939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12892264345121691340058341 2417299564710317126260939)
                ·
                  refine ⟨3625949347065475689391409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2417299564710317126260939 3625949347065475689391409)
                  ·
                    refine ⟨2719462010299106767043557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3625949347065475689391409 2719462010299106767043557)
                    ·
                      refine ⟨509899126931082518820667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2719462010299106767043557 509899126931082518820667)
                      ·
                        rfl

theorem cell23_993025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_993025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_993025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_993025 prefixEnd_993025 := by exact prefixLift 993025
  have htrace : WordTrace (prefixWord ++ tailWord_993025) baseStart_993025 baseEnd_993025 := by
    simpa [prefixWord, tailWord_993025, baseEnd_993025] using wordTrace_append hprefix tailTrace_993025
  have hstable : (prefixWord ++ tailWord_993025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993025).length < 2 ^ (prefixWord ++ tailWord_993025).sum := by decide
  have hdescent : baseEnd_993025 < baseStart_993025 := by decide
  rcases family_descends (prefixWord ++ tailWord_993025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993032 : List Nat := [2, 1, 3, 2, 2, 1, 1, 5, 1, 2, 3]
def baseStart_993032 : Nat := 118140960795 + 993032 * 2 ^ 59
def prefixEnd_993032 : Nat := 4983230072969 + 3 ^ 40 * 993032 * 2
def baseEnd_993032 : Nat := 509902721295663991433135

theorem tailTrace_993032 : CollatzResearch.WordTrace tailWord_993032 prefixEnd_993032 509902721295663991433135 := by
  unfold tailWord_993032
  simp only [CollatzResearch.WordTrace]
  refine ⟨18109426269211067604226675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24145901692281423472302233 18109426269211067604226675)
  ·
    refine ⟨27164139403816601406340013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18109426269211067604226675 27164139403816601406340013)
    ·
      refine ⟨10186552276431225527377505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27164139403816601406340013 10186552276431225527377505)
      ·
        refine ⟨7639914207323419145533129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10186552276431225527377505 7639914207323419145533129)
        ·
          refine ⟨5729935655492564359149847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7639914207323419145533129 5729935655492564359149847)
          ·
            refine ⟨8594903483238846538724771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5729935655492564359149847 8594903483238846538724771)
            ·
              refine ⟨12892355224858269808087157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8594903483238846538724771 12892355224858269808087157)
              ·
                refine ⟨1208658302330462794508171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12892355224858269808087157 1208658302330462794508171)
                ·
                  refine ⟨1812987453495694191762257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1208658302330462794508171 1812987453495694191762257)
                  ·
                    refine ⟨1359740590121770643821693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1812987453495694191762257 1359740590121770643821693)
                    ·
                      refine ⟨509902721295663991433135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1359740590121770643821693 509902721295663991433135)
                      ·
                        rfl

theorem cell23_993032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_993032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_993032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_993032 prefixEnd_993032 := by exact prefixLift 993032
  have htrace : WordTrace (prefixWord ++ tailWord_993032) baseStart_993032 baseEnd_993032 := by
    simpa [prefixWord, tailWord_993032, baseEnd_993032] using wordTrace_append hprefix tailTrace_993032
  have hstable : (prefixWord ++ tailWord_993032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993032).length < 2 ^ (prefixWord ++ tailWord_993032).sum := by decide
  have hdescent : baseEnd_993032 < baseStart_993032 := by decide
  rcases family_descends (prefixWord ++ tailWord_993032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993042 : List Nat := [3, 2, 4, 1, 1, 1, 1, 2, 1, 1, 6]
def baseStart_993042 : Nat := 118140960795 + 993042 * 2 ^ 59
def prefixEnd_993042 : Nat := 4983230072969 + 3 ^ 40 * 993042 * 2
def baseEnd_993042 : Nat := 509907856102208952308089

theorem tailTrace_993042 : CollatzResearch.WordTrace tailWord_993042 prefixEnd_993042 509907856102208952308089 := by
  unfold tailWord_993042
  simp only [CollatzResearch.WordTrace]
  refine ⟨9054804317096476729079345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24146144845590604610878253 9054804317096476729079345)
  ·
    refine ⟨6791103237822357546809509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9054804317096476729079345 6791103237822357546809509)
    ·
      refine ⟨1273331857091692040026783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6791103237822357546809509 1273331857091692040026783)
      ·
        refine ⟨1909997785637538060040175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1273331857091692040026783 1909997785637538060040175)
        ·
          refine ⟨2864996678456307090060263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1909997785637538060040175 2864996678456307090060263)
          ·
            refine ⟨4297495017684460635090395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2864996678456307090060263 4297495017684460635090395)
            ·
              refine ⟨6446242526526690952635593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4297495017684460635090395 6446242526526690952635593)
              ·
                refine ⟨4834681894895018214476695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6446242526526690952635593 4834681894895018214476695)
                ·
                  refine ⟨7252022842342527321715043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4834681894895018214476695 7252022842342527321715043)
                  ·
                    refine ⟨10878034263513790982572565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7252022842342527321715043 10878034263513790982572565)
                    ·
                      refine ⟨509907856102208952308089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10878034263513790982572565 509907856102208952308089)
                      ·
                        rfl

theorem cell23_993042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_993042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_993042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_993042 prefixEnd_993042 := by exact prefixLift 993042
  have htrace : WordTrace (prefixWord ++ tailWord_993042) baseStart_993042 baseEnd_993042 := by
    simpa [prefixWord, tailWord_993042, baseEnd_993042] using wordTrace_append hprefix tailTrace_993042
  have hstable : (prefixWord ++ tailWord_993042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993042).length < 2 ^ (prefixWord ++ tailWord_993042).sum := by decide
  have hdescent : baseEnd_993042 < baseStart_993042 := by decide
  rcases family_descends (prefixWord ++ tailWord_993042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993119 : List Nat := [1, 1, 2, 3, 1, 5, 2, 1, 1, 4, 2]
def baseStart_993119 : Nat := 118140960795 + 993119 * 2 ^ 59
def prefixEnd_993119 : Nat := 4983230072969 + 3 ^ 40 * 993119 * 2
def baseEnd_993119 : Nat := 509947394112605151045235

theorem tailTrace_993119 : CollatzResearch.WordTrace tailWord_993119 prefixEnd_993119 509947394112605151045235 := by
  unfold tailWord_993119
  simp only [CollatzResearch.WordTrace]
  refine ⟨36222025689106949066870411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24148017126071299377913607 36222025689106949066870411)
  ·
    refine ⟨54333038533660423600305617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36222025689106949066870411 54333038533660423600305617)
    ·
      refine ⟨40749778900245317700229213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54333038533660423600305617 40749778900245317700229213)
      ·
        refine ⟨15281167087591994137585955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40749778900245317700229213 15281167087591994137585955)
        ·
          refine ⟨22921750631387991206378933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15281167087591994137585955 22921750631387991206378933)
          ·
            refine ⟨2148914121692624175598025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22921750631387991206378933 2148914121692624175598025)
            ·
              refine ⟨1611685591269468131698519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2148914121692624175598025 1611685591269468131698519)
              ·
                refine ⟨2417528386904202197547779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1611685591269468131698519 2417528386904202197547779)
                ·
                  refine ⟨3626292580356303296321669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2417528386904202197547779 3626292580356303296321669)
                  ·
                    refine ⟨679929858816806868060313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3626292580356303296321669 679929858816806868060313)
                    ·
                      refine ⟨509947394112605151045235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 679929858816806868060313 509947394112605151045235)
                      ·
                        rfl

theorem cell23_993119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 4, 2].length) (baseStart_993119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_993119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_993119 prefixEnd_993119 := by exact prefixLift 993119
  have htrace : WordTrace (prefixWord ++ tailWord_993119) baseStart_993119 baseEnd_993119 := by
    simpa [prefixWord, tailWord_993119, baseEnd_993119] using wordTrace_append hprefix tailTrace_993119
  have hstable : (prefixWord ++ tailWord_993119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993119).length < 2 ^ (prefixWord ++ tailWord_993119).sum := by decide
  have hdescent : baseEnd_993119 < baseStart_993119 := by decide
  rcases family_descends (prefixWord ++ tailWord_993119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993153 : List Nat := [1, 2, 4, 4, 1, 1, 1, 1, 4, 2, 2]
def baseStart_993153 : Nat := 118140960795 + 993153 * 2 ^ 59
def prefixEnd_993153 : Nat := 4983230072969 + 3 ^ 40 * 993153 * 2
def baseEnd_993153 : Nat := 509964852454858018020079

theorem tailTrace_993153 : CollatzResearch.WordTrace tailWord_993153 prefixEnd_993153 509964852454858018020079 := by
  unfold tailWord_993153
  simp only [CollatzResearch.WordTrace]
  refine ⟨36223265770983772873608113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24148843847322515249072075 36223265770983772873608113)
  ·
    refine ⟨27167449328237829655206085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36223265770983772873608113 27167449328237829655206085)
    ·
      refine ⟨5093896749044593060351141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27167449328237829655206085 5093896749044593060351141)
      ·
        refine ⟨955105640445861198815839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5093896749044593060351141 955105640445861198815839)
        ·
          refine ⟨1432658460668791798223759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 955105640445861198815839 1432658460668791798223759)
          ·
            refine ⟨2148987691003187697335639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1432658460668791798223759 2148987691003187697335639)
            ·
              refine ⟨3223481536504781546003459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2148987691003187697335639 3223481536504781546003459)
              ·
                refine ⟨4835222304757172319005189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3223481536504781546003459 4835222304757172319005189)
                ·
                  refine ⟨906604182141969809813473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4835222304757172319005189 906604182141969809813473)
                  ·
                    refine ⟨679953136606477357360105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 906604182141969809813473 679953136606477357360105)
                    ·
                      refine ⟨509964852454858018020079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 679953136606477357360105 509964852454858018020079)
                      ·
                        rfl

theorem cell23_993153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_993153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_993153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_993153 prefixEnd_993153 := by exact prefixLift 993153
  have htrace : WordTrace (prefixWord ++ tailWord_993153) baseStart_993153 baseEnd_993153 := by
    simpa [prefixWord, tailWord_993153, baseEnd_993153] using wordTrace_append hprefix tailTrace_993153
  have hstable : (prefixWord ++ tailWord_993153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993153).length < 2 ^ (prefixWord ++ tailWord_993153).sum := by decide
  have hdescent : baseEnd_993153 < baseStart_993153 := by decide
  rcases family_descends (prefixWord ++ tailWord_993153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993170 : List Nat := [3, 2, 3, 2, 1, 2, 3, 1, 2, 2, 2]
def baseStart_993170 : Nat := 118140960795 + 993170 * 2 ^ 59
def prefixEnd_993170 : Nat := 4983230072969 + 3 ^ 40 * 993170 * 2
def baseEnd_993170 : Nat := 509973581625984451507501

theorem tailTrace_993170 : CollatzResearch.WordTrace tailWord_993170 prefixEnd_993170 509973581625984451507501 := by
  unfold tailWord_993170
  simp only [CollatzResearch.WordTrace]
  refine ⟨9055971452980546194244241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24149257207948123184651309 9055971452980546194244241)
  ·
    refine ⟨6791978589735409645683181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9055971452980546194244241 6791978589735409645683181)
    ·
      refine ⟨2546991971150778617131193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6791978589735409645683181 2546991971150778617131193)
      ·
        refine ⟨1910243978363083962848395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2546991971150778617131193 1910243978363083962848395)
        ·
          refine ⟨2865365967544625944272593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1910243978363083962848395 2865365967544625944272593)
          ·
            refine ⟨2149024475658469458204445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2865365967544625944272593 2149024475658469458204445)
            ·
              refine ⟨805884178371926046826667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2149024475658469458204445 805884178371926046826667)
              ·
                refine ⟨1208826267557889070240001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 805884178371926046826667 1208826267557889070240001)
                ·
                  refine ⟨906619700668416802680001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1208826267557889070240001 906619700668416802680001)
                  ·
                    refine ⟨679964775501312602010001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 906619700668416802680001 679964775501312602010001)
                    ·
                      refine ⟨509973581625984451507501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 679964775501312602010001 509973581625984451507501)
                      ·
                        rfl

theorem cell23_993170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_993170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_993170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_993170 prefixEnd_993170 := by exact prefixLift 993170
  have htrace : WordTrace (prefixWord ++ tailWord_993170) baseStart_993170 baseEnd_993170 := by
    simpa [prefixWord, tailWord_993170, baseEnd_993170] using wordTrace_append hprefix tailTrace_993170
  have hstable : (prefixWord ++ tailWord_993170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993170).length < 2 ^ (prefixWord ++ tailWord_993170).sum := by decide
  have hdescent : baseEnd_993170 < baseStart_993170 := by decide
  rcases family_descends (prefixWord ++ tailWord_993170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993172 : List Nat := [2, 4, 2, 1, 1, 2, 1, 2, 1, 7]
def baseStart_993172 : Nat := 118140960795 + 993172 * 2 ^ 59
def prefixEnd_993172 : Nat := 4983230072969 + 3 ^ 40 * 993172 * 2
def baseEnd_993172 : Nat := 169991536195764481227497

theorem tailTrace_993172 : CollatzResearch.WordTrace tailWord_993172 prefixEnd_993172 169991536195764481227497 := by
  unfold tailWord_993172
  simp only [CollatzResearch.WordTrace]
  refine ⟨18111979378957469559274885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24149305838609959412366513 18111979378957469559274885)
  ·
    refine ⟨3395996133554525542364041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18111979378957469559274885 3395996133554525542364041)
    ·
      refine ⟨2546997100165894156773031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3395996133554525542364041 2546997100165894156773031)
      ·
        refine ⟨3820495650248841235159547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2546997100165894156773031 3820495650248841235159547)
        ·
          refine ⟨5730743475373261852739321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3820495650248841235159547 5730743475373261852739321)
          ·
            refine ⟨4298057606529946389554491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5730743475373261852739321 4298057606529946389554491)
            ·
              refine ⟨6447086409794919584331737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4298057606529946389554491 6447086409794919584331737)
              ·
                refine ⟨4835314807346189688248803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6447086409794919584331737 4835314807346189688248803)
                ·
                  refine ⟨7252972211019284532373205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4835314807346189688248803 7252972211019284532373205)
                  ·
                    refine ⟨169991536195764481227497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7252972211019284532373205 169991536195764481227497)
                    ·
                      rfl

theorem cell23_993172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_993172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_993172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_993172 prefixEnd_993172 := by exact prefixLift 993172
  have htrace : WordTrace (prefixWord ++ tailWord_993172) baseStart_993172 baseEnd_993172 := by
    simpa [prefixWord, tailWord_993172, baseEnd_993172] using wordTrace_append hprefix tailTrace_993172
  have hstable : (prefixWord ++ tailWord_993172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993172).length < 2 ^ (prefixWord ++ tailWord_993172).sum := by decide
  have hdescent : baseEnd_993172 < baseStart_993172 := by decide
  rcases family_descends (prefixWord ++ tailWord_993172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993202 : List Nat := [3, 2, 1, 1, 1, 1, 1, 4, 5, 4]
def baseStart_993202 : Nat := 118140960795 + 993202 * 2 ^ 59
def prefixEnd_993202 : Nat := 4983230072969 + 3 ^ 40 * 993202 * 2
def baseEnd_993202 : Nat := 169996671002309442102451

theorem tailTrace_993202 : CollatzResearch.WordTrace tailWord_993202 prefixEnd_993202 169996671002309442102451 := by
  unfold tailWord_993202
  simp only [CollatzResearch.WordTrace]
  refine ⟨9056263236951563560535465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24150035298537502828094573 9056263236951563560535465)
  ·
    refine ⟨6792197427713672670401599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9056263236951563560535465 6792197427713672670401599)
    ·
      refine ⟨10188296141570509005602399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6792197427713672670401599 10188296141570509005602399)
      ·
        refine ⟨15282444212355763508403599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10188296141570509005602399 15282444212355763508403599)
        ·
          refine ⟨22923666318533645262605399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15282444212355763508403599 22923666318533645262605399)
          ·
            refine ⟨34385499477800467893908099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22923666318533645262605399 34385499477800467893908099)
            ·
              refine ⟨51578249216700701840862149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34385499477800467893908099 51578249216700701840862149)
              ·
                refine ⟨9670921728131381595161653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51578249216700701840862149 9670921728131381595161653)
                ·
                  refine ⟨906648912012317024546405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9670921728131381595161653 906648912012317024546405)
                  ·
                    refine ⟨169996671002309442102451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 906648912012317024546405 169996671002309442102451)
                    ·
                      rfl

theorem cell23_993202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 5, 4].length) (baseStart_993202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_993202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_993202 prefixEnd_993202 := by exact prefixLift 993202
  have htrace : WordTrace (prefixWord ++ tailWord_993202) baseStart_993202 baseEnd_993202 := by
    simpa [prefixWord, tailWord_993202, baseEnd_993202] using wordTrace_append hprefix tailTrace_993202
  have hstable : (prefixWord ++ tailWord_993202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993202).length < 2 ^ (prefixWord ++ tailWord_993202).sum := by decide
  have hdescent : baseEnd_993202 < baseStart_993202 := by decide
  rcases family_descends (prefixWord ++ tailWord_993202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993215 : List Nat := [1, 1, 2, 2, 2, 1, 3, 3, 8]
def baseStart_993215 : Nat := 118140960795 + 993215 * 2 ^ 59
def prefixEnd_993215 : Nat := 4983230072969 + 3 ^ 40 * 993215 * 2
def baseEnd_993215 : Nat := 56666298695048530604977

theorem tailTrace_993215 : CollatzResearch.WordTrace tailWord_993215 prefixEnd_993215 56666298695048530604977 := by
  unfold tailWord_993215
  simp only [CollatzResearch.WordTrace]
  refine ⟨36225527096759157462365099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24150351397839438308243399 36225527096759157462365099)
  ·
    refine ⟨54338290645138736193547649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36225527096759157462365099 54338290645138736193547649)
    ·
      refine ⟨40753717983854052145160737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54338290645138736193547649 40753717983854052145160737)
      ·
        refine ⟨30565288487890539108870553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40753717983854052145160737 30565288487890539108870553)
        ·
          refine ⟨22923966365917904331652915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30565288487890539108870553 22923966365917904331652915)
          ·
            refine ⟨34385949548876856497479373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22923966365917904331652915 34385949548876856497479373)
            ·
              refine ⟨12894731080828821186554765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34385949548876856497479373 12894731080828821186554765)
              ·
                refine ⟨4835524155310807944958037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12894731080828821186554765 4835524155310807944958037)
                ·
                  refine ⟨56666298695048530604977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4835524155310807944958037 56666298695048530604977)
                  ·
                    rfl

theorem cell23_993215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 8].length) (baseStart_993215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_993215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_993215 prefixEnd_993215 := by exact prefixLift 993215
  have htrace : WordTrace (prefixWord ++ tailWord_993215) baseStart_993215 baseEnd_993215 := by
    simpa [prefixWord, tailWord_993215, baseEnd_993215] using wordTrace_append hprefix tailTrace_993215
  have hstable : (prefixWord ++ tailWord_993215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993215).length < 2 ^ (prefixWord ++ tailWord_993215).sum := by decide
  have hdescent : baseEnd_993215 < baseStart_993215 := by decide
  rcases family_descends (prefixWord ++ tailWord_993215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993309 : List Nat := [1, 4, 2, 2, 2, 1, 2, 2, 1, 6]
def baseStart_993309 : Nat := 118140960795 + 993309 * 2 ^ 59
def prefixEnd_993309 : Nat := 4983230072969 + 3 ^ 40 * 993309 * 2
def baseEnd_993309 : Nat := 170014985145653135889787

theorem tailTrace_993309 : CollatzResearch.WordTrace tailWord_993309 prefixEnd_993309 170014985145653135889787 := by
  unfold tailWord_993309
  simp only [CollatzResearch.WordTrace]
  refine ⟨36228955558418611516286981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24152637038945741010857987 36228955558418611516286981)
  ·
    refine ⟨6792929167203489659303809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36228955558418611516286981 6792929167203489659303809)
    ·
      refine ⟨5094696875402617244477857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6792929167203489659303809 5094696875402617244477857)
      ·
        refine ⟨3821022656551962933358393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5094696875402617244477857 3821022656551962933358393)
        ·
          refine ⟨2865766992413972200018795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3821022656551962933358393 2865766992413972200018795)
          ·
            refine ⟨4298650488620958300028193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2865766992413972200018795 4298650488620958300028193)
            ·
              refine ⟨3223987866465718725021145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4298650488620958300028193 3223987866465718725021145)
              ·
                refine ⟨2417990899849289043765859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3223987866465718725021145 2417990899849289043765859)
                ·
                  refine ⟨3626986349773933565648789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2417990899849289043765859 3626986349773933565648789)
                  ·
                    refine ⟨170014985145653135889787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3626986349773933565648789 170014985145653135889787)
                    ·
                      rfl

theorem cell23_993309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_993309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_993309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_993309 prefixEnd_993309 := by exact prefixLift 993309
  have htrace : WordTrace (prefixWord ++ tailWord_993309) baseStart_993309 baseEnd_993309 := by
    simpa [prefixWord, tailWord_993309, baseEnd_993309] using wordTrace_append hprefix tailTrace_993309
  have hstable : (prefixWord ++ tailWord_993309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993309).length < 2 ^ (prefixWord ++ tailWord_993309).sum := by decide
  have hdescent : baseEnd_993309 < baseStart_993309 := by decide
  rcases family_descends (prefixWord ++ tailWord_993309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993313 : List Nat := [1, 2, 3, 2, 4, 2, 2, 1, 1, 5]
def baseStart_993313 : Nat := 118140960795 + 993313 * 2 ^ 59
def prefixEnd_993313 : Nat := 4983230072969 + 3 ^ 40 * 993313 * 2
def baseEnd_993313 : Nat := 170015669786525797339781

theorem tailTrace_993313 : CollatzResearch.WordTrace tailWord_993313 prefixEnd_993313 170015669786525797339781 := by
  unfold tailWord_993313
  simp only [CollatzResearch.WordTrace]
  refine ⟨36229101450404120199432593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24152734300269413466288395 36229101450404120199432593)
  ·
    refine ⟨27171826087803090149574445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36229101450404120199432593 27171826087803090149574445)
    ·
      refine ⟨10189434782926158806090417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27171826087803090149574445 10189434782926158806090417)
      ·
        refine ⟨7642076087194619104567813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10189434782926158806090417 7642076087194619104567813)
        ·
          refine ⟨1432889266348991082106465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7642076087194619104567813 1432889266348991082106465)
          ·
            refine ⟨1074666949761743311579849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1432889266348991082106465 1074666949761743311579849)
            ·
              refine ⟨806000212321307483684887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1074666949761743311579849 806000212321307483684887)
              ·
                refine ⟨1209000318481961225527331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 806000212321307483684887 1209000318481961225527331)
                ·
                  refine ⟨1813500477722941838290997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1209000318481961225527331 1813500477722941838290997)
                  ·
                    refine ⟨170015669786525797339781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1813500477722941838290997 170015669786525797339781)
                    ·
                      rfl

theorem cell23_993313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 1, 1, 5].length) (baseStart_993313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_993313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_993313 prefixEnd_993313 := by exact prefixLift 993313
  have htrace : WordTrace (prefixWord ++ tailWord_993313) baseStart_993313 baseEnd_993313 := by
    simpa [prefixWord, tailWord_993313, baseEnd_993313] using wordTrace_append hprefix tailTrace_993313
  have hstable : (prefixWord ++ tailWord_993313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993313).length < 2 ^ (prefixWord ++ tailWord_993313).sum := by decide
  have hdescent : baseEnd_993313 < baseStart_993313 := by decide
  rcases family_descends (prefixWord ++ tailWord_993313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_993326 : List Nat := [4, 1, 3, 1, 1, 3, 1, 1, 4, 4]
def baseStart_993326 : Nat := 118140960795 + 993326 * 2 ^ 59
def prefixEnd_993326 : Nat := 4983230072969 + 3 ^ 40 * 993326 * 2
def baseEnd_993326 : Nat := 170017894869361947052261

theorem tailTrace_993326 : CollatzResearch.WordTrace tailWord_993326 prefixEnd_993326 170017894869361947052261 := by
  unfold tailWord_993326
  simp only [CollatzResearch.WordTrace]
  refine ⟨4528696949919627927456979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24153050399571348946437221 4528696949919627927456979)
  ·
    refine ⟨6793045424879441891185469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4528696949919627927456979 6793045424879441891185469)
    ·
      refine ⟨2547392034329790709194551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6793045424879441891185469 2547392034329790709194551)
      ·
        refine ⟨3821088051494686063791827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2547392034329790709194551 3821088051494686063791827)
        ·
          refine ⟨5731632077242029095687741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3821088051494686063791827 5731632077242029095687741)
          ·
            refine ⟨2149362028965760910882903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5731632077242029095687741 2149362028965760910882903)
            ·
              refine ⟨3224043043448641366324355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2149362028965760910882903 3224043043448641366324355)
              ·
                refine ⟨4836064565172962049486533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3224043043448641366324355 4836064565172962049486533)
                ·
                  refine ⟨906762105969930384278725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4836064565172962049486533 906762105969930384278725)
                  ·
                    refine ⟨170017894869361947052261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 906762105969930384278725 170017894869361947052261)
                    ·
                      rfl

theorem cell23_993326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_993326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_993326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_993326 prefixEnd_993326 := by exact prefixLift 993326
  have htrace : WordTrace (prefixWord ++ tailWord_993326) baseStart_993326 baseEnd_993326 := by
    simpa [prefixWord, tailWord_993326, baseEnd_993326] using wordTrace_append hprefix tailTrace_993326
  have hstable : (prefixWord ++ tailWord_993326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_993326).length < 2 ^ (prefixWord ++ tailWord_993326).sum := by decide
  have hdescent : baseEnd_993326 < baseStart_993326 := by decide
  rcases family_descends (prefixWord ++ tailWord_993326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
